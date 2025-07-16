use alloc::string::ToString;
use axalloc::GlobalPage;
use axhal::mem::{PhysAddrRange, VirtAddrRange, virt_to_phys};
use axhal::paging::MappingFlags;
use axmm::kernel_aspace;
use base_task::{BaseTaskRef, Scheduler, WeakBaseTaskRef};
use core::{cell::UnsafeCell, mem::MaybeUninit, str::from_utf8};
use memory_addr::align_up_4k;

use xmas_elf::program::SegmentData;

const VSCHED_VA_BASE: usize = 0xFFFF_0000_0000;

core::arch::global_asm!(
    r#"
.globl vsched_start, vsched_end
.balign 0x1000
.section .text.vsched
vsched_start:
	.incbin "vsched-axtask/libvsched.so"
	.balign 0x1000
vsched_end:
    "#,
);

unsafe extern "C" {
    fn vsched_start();
    fn vsched_end();
}

#[allow(unused)]
pub struct Vsched {
    data_area: GlobalPage,
    text_range: PhysAddrRange,
}

pub fn map_vsched() -> Result<Vsched, axerrno::AxError> {
    let vsched_start_va = vsched_start as usize;
    let vsched_end_va = vsched_end as usize;
    let vsched_size = vsched_end_va - vsched_start_va;
    let vsched_so =
        unsafe { core::slice::from_raw_parts(vsched_start_va as *const u8, vsched_size) };

    let vsched_elf = xmas_elf::ElfFile::new(vsched_so).expect("Error parsing app ELF file.");
    if let Some(interp) = vsched_elf
        .program_iter()
        .find(|ph| ph.get_type() == Ok(xmas_elf::program::Type::Interp))
    {
        let interp = match interp.get_data(&vsched_elf) {
            Ok(SegmentData::Undefined(data)) => data,
            _ => panic!("Invalid data in Interp Elf Program Header"),
        };

        let interp_path = from_utf8(interp).expect("Interpreter path isn't valid UTF-8");
        // remove trailing '\0'
        let _interp_path = interp_path.trim_matches(char::from(0)).to_string();
        debug!("Interpreter path: {:?}", _interp_path);
    }
    let mut kernel_aspace = kernel_aspace().lock();
    let map_start = kernel_aspace
        .find_free_area(
            VSCHED_VA_BASE.into(),
            vsched_size + VSCHED_DATA_SIZE,
            VirtAddrRange::from_start_size(kernel_aspace.base(), kernel_aspace.size()),
        )
        .unwrap();
    info!(
        "vsched base {:?}, vsched data size {:#x?}, RQ_CAP {}, SMP {}",
        map_start,
        VSCHED_DATA_SIZE,
        config::RQ_CAP,
        config::SMP
    );
    let elf_base_addr = map_start.as_usize() + VSCHED_DATA_SIZE;
    // let relocate_pairs = elf_parser::get_relocate_pairs(&elf, elf_base_addr);
    let segments = kernel_elf_parser::get_elf_segments(&vsched_elf, elf_base_addr);
    let relocate_pairs = kernel_elf_parser::get_relocate_pairs(&vsched_elf, elf_base_addr);
    // map the data section.
    let mut vsched_data_area = GlobalPage::alloc_contiguous(
        VSCHED_DATA_SIZE / config::PAGES_SIZE_4K,
        config::PAGES_SIZE_4K,
    )
    .unwrap();
    vsched_data_area.zero();
    kernel_aspace
        .map_linear(
            map_start,
            virt_to_phys(vsched_data_area.start_vaddr()),
            VSCHED_DATA_SIZE,
            MappingFlags::READ | MappingFlags::WRITE,
        )
        .unwrap();
    for segment in segments {
        let offset = segment.vaddr.as_usize() - elf_base_addr;
        let mut flags = MappingFlags::from_bits(segment.flags.bits()).unwrap();
        flags.remove(MappingFlags::USER);
        if flags.contains(MappingFlags::WRITE) {
            kernel_aspace
                .map_alloc(
                    segment.vaddr.as_usize().into(),
                    align_up_4k(segment.size),
                    flags,
                    true,
                )
                .unwrap();
            kernel_aspace
                .write(segment.vaddr.as_usize().into(), &segment.data.unwrap())
                .unwrap();
        } else {
            kernel_aspace
                .map_linear(
                    segment.vaddr.as_usize().into(),
                    virt_to_phys((vsched_start_va + offset).into()),
                    align_up_4k(segment.size),
                    flags,
                )
                .unwrap();
        }
    }

    for relocate_pair in relocate_pairs {
        let src: usize = relocate_pair.src.into();
        let dst: usize = relocate_pair.dst.into();
        let count = relocate_pair.count;
        trace!(
            "Relocate: src: 0x{:x}, dst: 0x{:x}, count: {}",
            src, dst, count
        );
        unsafe { core::ptr::copy_nonoverlapping(src.to_ne_bytes().as_ptr(), dst as *mut u8, count) }
    }

    unsafe { vsched_apis::init_vsched_vtable(elf_base_addr as _, &vsched_elf) };

    Ok(Vsched {
        data_area: vsched_data_area,
        text_range: PhysAddrRange::from_start_size(
            virt_to_phys(vsched_start_va.into()),
            vsched_size,
        ),
    })
}

const VSCHED_DATA_SIZE: usize = config::SMP
    * ((core::mem::size_of::<PerCPU>() + config::PAGES_SIZE_4K - 1)
        & (!(config::PAGES_SIZE_4K - 1)));

#[allow(unused)]
#[repr(C)]
pub struct PerCPU {
    /// The ID of the CPU this run queue is associated with.
    pub cpu_id: usize,
    /// The core scheduler of this run queue.
    /// Since irq and preempt are preserved by the kernel guard hold by `AxRunQueueRef`,
    /// we just use a simple raw spin lock here.
    pub scheduler: Scheduler,

    pub current_task: UnsafeCell<BaseTaskRef>,

    pub idle_task: BaseTaskRef,
    /// Stores the weak reference to the previous task that is running on this CPU.
    pub prev_task: UnsafeCell<MaybeUninit<WeakBaseTaskRef>>,
}
