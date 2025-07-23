use alloc::string::ToString;
use axhal::mem::{PhysAddrRange, VirtAddrRange, virt_to_phys};
use axhal::paging::MappingFlags;
use axmm::kernel_aspace;
use base_task::{TaskInner, percpu_size_4k_aligned};
use core::str::from_utf8;
use memory_addr::{align_down_4k, align_up_4k};

use xmas_elf::program::SegmentData;

const VSCHED_VA_BASE: usize = 0xFFFF_0000_0000;
const VSCHED_DATA_SIZE: usize = config::SMP * percpu_size_4k_aligned::<TaskInner>();

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
    kernel_aspace
        .map_alloc(
            map_start,
            VSCHED_DATA_SIZE,
            MappingFlags::READ | MappingFlags::WRITE,
            true,
        )
        .unwrap();

    let elf_base_addr = map_start.as_usize() + VSCHED_DATA_SIZE;
    let parser = kernel_elf_parser::ELFParser::new(
        &vsched_elf,
        0,
        Some((map_start.as_usize() + VSCHED_DATA_SIZE) as _),
        0,
    )
    .unwrap();
    for segment in &mut parser.ph_load() {
        trace!(
            "Mapping ELF segment: [{:#x?}, {:#x?}) offset: {:#x?} memsz {:#x?} filesz {:#x?} flags: {:#x?}",
            segment.vaddr,
            segment.vaddr + segment.memsz as usize,
            segment.offset,
            segment.memsz,
            segment.filesz,
            segment.flags
        );
        segment.flags.remove(MappingFlags::USER);
        let start = align_down_4k(segment.vaddr.into());
        let end = align_up_4k(segment.vaddr.as_usize() + segment.memsz as usize);
        let size = end - start;
        if size > 0 {
            kernel_aspace.map_alloc(start.into(), size, segment.flags, true)?;

            let data = unsafe {
                core::slice::from_raw_parts(
                    (vsched_start_va + segment.offset) as *const u8,
                    segment.filesz as _,
                )
            };
            kernel_aspace
                .write(segment.vaddr.as_usize().into(), data)
                .unwrap();
        }
    }

    let relocate_pairs = elf_parser::get_relocate_pairs(&vsched_elf, Some(elf_base_addr));

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
        text_range: PhysAddrRange::from_start_size(
            virt_to_phys(vsched_start_va.into()),
            vsched_size,
        ),
    })
}
