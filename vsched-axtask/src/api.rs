//! Task APIs for multi-task configuration.

use alloc::sync::Arc;

use alloc::string::String;
use base_task::{AxTask, TaskRef};
use kernel_guard::NoPreemptIrqSave;

pub(crate) use crate::run_queue::current_guard;
use crate::task::{CurrentTask, Task};
#[doc(cfg(feature = "multitask"))]
pub use crate::wait_queue::*;
#[doc(cfg(feature = "multitask"))]
pub use base_task::{TaskExtMut, TaskExtRef};
#[doc(cfg(feature = "multitask"))]
pub use base_task::{TaskId, TaskInner};

pub type AxTaskRef = Arc<AxTask>;
/// The wrapper type for [`cpumask::CpuMask`] with SMP configuration.
pub type AxCpuMask = cpumask::CpuMask<{ axconfig::plat::CPU_NUM }>;

#[percpu::def_percpu]
static THIS_CPU_ID: usize = 0;

pub(crate) fn this_cpu_id() -> usize {
    // Do not use the `NoPreemptIrqSave`, otherwise it will cause recursive
    let _gurad = kernel_guard::IrqSave::new();
    unsafe { THIS_CPU_ID.read_current_raw() }
}

pub(crate) fn set_cpu_id(cpu_id: usize) {
    unsafe {
        THIS_CPU_ID.write_current_raw(cpu_id);
    }
}

#[cfg(feature = "preempt")]
struct KernelGuardIfImpl;

#[cfg(feature = "preempt")]
#[crate_interface::impl_interface]
impl kernel_guard::KernelGuardIf for KernelGuardIfImpl {
    fn disable_preempt() {
        if let Some(curr) = current_may_uninit() {
            curr.disable_preempt();
        }
    }

    fn enable_preempt() {
        if let Some(curr) = current_may_uninit() {
            curr.enable_preempt(true);
        }
    }
}

/// Gets the current task, or returns [`None`] if the current task is not
/// initialized.
pub fn current_may_uninit() -> Option<CurrentTask> {
    CurrentTask::try_get()
}

/// Gets the current task.
///
/// # Panics
///
/// Panics if the current task is not initialized.
pub fn current() -> CurrentTask {
    CurrentTask::get()
}

/// Initializes the task scheduler (for the primary CPU).
pub fn init_scheduler() {
    info!("Initialize scheduling...");
    crate::run_queue::init();
    #[cfg(feature = "irq")]
    crate::timers::init();

    info!(
        "  use {} scheduler.",
        base_task::Scheduler::scheduler_name()
    );
}

/// Initializes the task scheduler for secondary CPUs.
pub fn init_scheduler_secondary() {
    crate::run_queue::init_secondary();
    #[cfg(feature = "irq")]
    crate::timers::init();
}

/// Handles periodic timer ticks for the task manager.
///
/// For example, advance scheduler states, checks timed events, etc.
#[cfg(feature = "irq")]
#[doc(cfg(feature = "irq"))]
pub fn on_timer_tick() {
    use kernel_guard::NoOp;
    crate::timers::check_events();
    // Since irq and preemption are both disabled here,
    // we can get current run queue with the default `kernel_guard::NoOp`.
    current_guard::<NoOp>().scheduler_timer_tick();
}

/// Adds the given task to the run queue, returns the task reference.
pub fn spawn_task(task_ref: TaskRef) -> AxTaskRef {
    current_guard::<NoPreemptIrqSave>().add_task(task_ref)
}

/// Spawns a new task with the given parameters.
///
/// Returns the task reference.
pub fn spawn_raw<F>(f: F, name: String, stack_size: usize) -> AxTaskRef
where
    F: FnOnce() + Send + 'static,
{
    spawn_task(Task::new(f, name, stack_size))
}

/// Spawns a new coroutine task with the given future and name.
///
/// Returns the task reference.
pub fn spawn_raw_f<F>(f: F, name: String) -> AxTaskRef
where
    F: Future<Output = ()> + Send + 'static,
{
    spawn_task(Task::new_f(f, name))
}

/// Spawns a new task with the default parameters.
///
/// The default task name is an empty string. The default task stack size is
/// [`axconfig::TASK_STACK_SIZE`].
///
/// Returns the task reference.
pub fn spawn<F>(f: F) -> AxTaskRef
where
    F: FnOnce() + Send + 'static,
{
    spawn_raw(f, "".into(), axconfig::TASK_STACK_SIZE)
}

/// Spawns a new coroutine task with the default parameters.
///
/// The default task name is an empty string.
///
/// Returns the task reference.
pub fn spawn_f<F>(f: F) -> AxTaskRef
where
    F: Future<Output = ()> + Send + 'static,
{
    spawn_raw_f(f, "".into())
}

/// Set the priority for current task.
///
/// The range of the priority is dependent on the underlying scheduler. For
/// example, in the [CFS] scheduler, the priority is the nice value, ranging from
/// -20 to 19.
///
/// Returns `true` if the priority is set successfully.
///
/// [CFS]: https://en.wikipedia.org/wiki/Completely_Fair_Scheduler
pub fn set_priority(prio: isize) -> bool {
    current_guard::<NoPreemptIrqSave>().set_current_priority(prio)
}

/// Set the affinity for the current task.
/// [`AxCpuMask`] is used to specify the CPU affinity.
/// Returns `true` if the affinity is set successfully.
///
/// TODO: support set the affinity for other tasks.
pub fn set_current_affinity(cpumask: AxCpuMask) -> bool {
    if cpumask.is_empty() {
        false
    } else {
        let curr = current();

        curr.set_cpumask(cpumask);
        // After setting the affinity, we need to check if current cpu matches
        // the affinity. If not, we need to migrate the task to the correct CPU.
        #[cfg(feature = "smp")]
        if !cpumask.get(this_cpu_id()) {
            const MIGRATION_TASK_STACK_SIZE: usize = 4096;
            // Spawn a new migration task for migrating.
            let migration_task = Task::new(
                move || crate::run_queue::migrate_entry(curr.clone()),
                "migration-task".into(),
                MIGRATION_TASK_STACK_SIZE,
            );

            // Migrate the current task to the correct CPU using the migration task.
            current_guard::<NoPreemptIrqSave>().migrate_current(migration_task);

            assert!(cpumask.get(this_cpu_id()), "Migration failed");
        }
        true
    }
}

/// Current task gives up the CPU time voluntarily, and switches to another
/// ready task.
pub fn yield_now() {
    current_guard::<NoPreemptIrqSave>().yield_current()
}

/// Current coroutine task gives up the CPU time voluntarily, and switches to another
/// ready task.
#[inline]
pub async fn yield_now_f() {
    crate::run_queue::YieldFuture::<NoPreemptIrqSave>::new().await;
}

/// Current coroutine task is going to sleep for the given duration.
///
/// If the feature `irq` is not enabled, it uses busy-wait instead.
pub async fn sleep_f(dur: core::time::Duration) {
    sleep_until_f(axhal::time::wall_time() + dur).await;
}

/// Current task is going to sleep for the given duration.
///
/// If the feature `irq` is not enabled, it uses busy-wait instead.
pub fn sleep(dur: core::time::Duration) {
    sleep_until(axhal::time::wall_time() + dur);
}

/// Current task is going to sleep, it will be woken up at the given deadline.
///
/// If the feature `irq` is not enabled, it uses busy-wait instead.
pub fn sleep_until(deadline: axhal::time::TimeValue) {
    #[cfg(feature = "irq")]
    current_guard::<NoPreemptIrqSave>().sleep_until(deadline);
    #[cfg(not(feature = "irq"))]
    axhal::time::busy_wait_until(deadline);
}

/// Current coroutine task is going to sleep, it will be woken up at the given deadline.
///
/// If the feature `irq` is not enabled, it uses busy-wait instead.
pub async fn sleep_until_f(deadline: axhal::time::TimeValue) {
    #[cfg(feature = "irq")]
    crate::run_queue::SleepUntilFuture::<NoPreemptIrqSave>::new(deadline).await;
    #[cfg(not(feature = "irq"))]
    axhal::time::busy_wait_until(deadline);
}

/// Exits the current task.
pub fn exit(exit_code: i32) -> ! {
    current_guard::<NoPreemptIrqSave>().exit_current(exit_code)
}

/// Exits the current coroutine task.
pub async fn exit_f(exit_code: i32) {
    crate::run_queue::ExitFuture::<NoPreemptIrqSave>::new(exit_code).await;
}

/// The idle task routine.
///
/// It runs an infinite loop that keeps calling [`yield_now()`].
pub fn run_idle() -> ! {
    loop {
        yield_now();
        debug!("idle task: waiting for IRQs...");
        #[cfg(feature = "irq")]
        axhal::asm::wait_for_irqs();
    }
}
