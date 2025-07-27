use alloc::collections::VecDeque;
use alloc::sync::Arc;
use core::future::Future;
use core::mem::ManuallyDrop;
use core::pin::Pin;
use core::task::{Context, Poll};

use kernel_guard::BaseGuard;

use crate::task::Task;
use axhal::percpu::this_cpu_id;

use crate::{AxCpuMask, AxTaskRef, WaitQueue, WaitQueueGuard};
use base_task::{TaskRef, TaskState};

macro_rules! percpu_static {
    ($(
        $(#[$comment:meta])*
        $name:ident: $ty:ty = $init:expr
    ),* $(,)?) => {
        $(
            $(#[$comment])*
            #[percpu::def_percpu]
            static $name: $ty = $init;
        )*
    };
}

percpu_static! {
    EXITED_TASKS: VecDeque<TaskRef> = VecDeque::new(),
    WAIT_FOR_EXIT: WaitQueue = WaitQueue::new(),
}

/// Get the specific guard.
///
/// Note:
/// in which scheduling operations can be performed.
pub(crate) struct CurrentGuard<G: BaseGuard> {
    state: G::State,
    _phantom: core::marker::PhantomData<G>,
}

#[inline(always)]
pub(crate) fn current_guard<G: BaseGuard>() -> CurrentGuard<G> {
    let irq_state = G::acquire();
    CurrentGuard {
        state: irq_state,
        _phantom: core::marker::PhantomData,
    }
}

impl<G: BaseGuard> Drop for CurrentGuard<G> {
    fn drop(&mut self) {
        G::release(self.state);
    }
}

/// Management operations for run queue, including adding tasks, unblocking tasks, etc.
impl<G: BaseGuard> CurrentGuard<G> {
    /// Adds a task to the scheduler.
    ///
    /// This function is used to add a new task to the scheduler.
    pub fn add_task(&mut self, task: TaskRef) -> AxTaskRef {
        assert!(task.is_ready());
        let cpu_id = task.select_run_queue_index();
        let task_clone = ManuallyDrop::into_inner(task.into_arc().clone());
        debug!("task add: {} on run_queue {}", task.id_name(), cpu_id);
        vsched_apis::spawn(cpu_id, task.clone());
        task_clone
    }

    /// Unblock one task by inserting it into the run queue.
    ///
    /// This function does nothing if the task is not in [`TaskState::Blocked`],
    /// which means the task is already unblocked by other cores.
    pub fn unblock_task(&mut self, task: TaskRef, resched: bool) {
        let task_id_name = task.id_name();
        let cpu_id = this_cpu_id();
        let dst_cpu_id = task.select_run_queue_index();
        debug!("task unblock: {} on run_queue {}", task_id_name, dst_cpu_id);
        vsched_apis::unblock_task(task, resched, dst_cpu_id, cpu_id);
    }
}

/// Core functions of run queue.
impl<G: BaseGuard> CurrentGuard<G> {
    #[cfg(feature = "irq")]
    pub fn scheduler_timer_tick(&mut self) {
        let cpu_id = this_cpu_id();
        let curr = vsched_apis::current(cpu_id);
        if !curr.is_idle() && vsched_apis::task_tick(cpu_id, &curr) {
            #[cfg(feature = "preempt")]
            curr.set_preempt_pending(true);
        }
    }

    /// Yield the current task and reschedule.
    /// This function will put the current task into this run queue with `Ready` state,
    /// and reschedule to the next task on this run queue.
    pub fn yield_current(&mut self) {
        let cpu_id = this_cpu_id();
        let curr = vsched_apis::current(cpu_id);
        trace!("task yield: {}", curr.id_name());
        assert!(curr.is_running());
        vsched_apis::yield_now(cpu_id);
        vsched_apis::clear_prev_task_on_cpu(this_cpu_id());
    }

    #[cfg(feature = "smp")]
    fn migrate_entry(&mut self, migrated_task: TaskRef) {
        let cpu_id = migrated_task.select_run_queue_index();
        vsched_apis::migrate_entry(cpu_id, migrated_task);
    }

    /// Migrate the current task to a new run queue matching its CPU affinity and reschedule.
    /// This function will spawn a new `migration_task` to perform the migration, which will set
    /// current task to `Ready` state and select a proper run queue for it according to its CPU affinity,
    /// switch to the migration task immediately after migration task is prepared.
    ///
    /// Note: the ownership if migrating task (which is current task) is handed over to the migration task,
    /// before the migration task inserted it into the target run queue.
    #[cfg(feature = "smp")]
    pub fn migrate_current(&mut self, migration_task: TaskRef) {
        let cpu_id = this_cpu_id();
        let curr = vsched_apis::current(cpu_id);
        trace!("task migrate: {}", curr.id_name());
        assert!(curr.is_running());

        // Mark current task's state as `Ready`,
        // but, do not put current task to the scheduler of this run queue.
        curr.set_state(TaskState::Ready);

        // Call `switch_to` to reschedule to the migration task that performs the migration directly.
        vsched_apis::switch_to(cpu_id, &curr, migration_task);
        vsched_apis::clear_prev_task_on_cpu(this_cpu_id());
    }

    /// Preempts the current task and reschedules.
    /// This function is used to preempt the current task and reschedule
    /// to next task on current run queue.
    ///
    /// This function is called by `current_check_preempt_pending` with IRQs and preemption disabled.
    ///
    /// Note:
    /// preemption may happened in `enable_preempt`, which is called
    /// each time a [`kspin::NoPreemptGuard`] is dropped.
    #[cfg(feature = "preempt")]
    pub fn preempt_resched(&mut self) {
        // There is no need to disable IRQ and preemption here, because
        // they both have been disabled in `current_check_preempt_pending`.
        let cpu_id = this_cpu_id();
        let curr = vsched_apis::current(cpu_id);
        assert!(curr.is_running());

        // When we call `preempt_resched()`, both IRQs and preemption must
        // have been disabled by `kernel_guard::NoPreemptIrqSave`. So we need
        // to set `current_disable_count` to 1 in `can_preempt()` to obtain
        // the preemption permission.
        let can_preempt = curr.can_preempt(1);

        debug!(
            "current task is to be preempted: {}, allow={}",
            curr.id_name(),
            can_preempt
        );
        if can_preempt {
            vsched_apis::preempt_current(cpu_id);
            vsched_apis::clear_prev_task_on_cpu(this_cpu_id());
        } else {
            curr.set_preempt_pending(true);
        }
    }

    /// Exit the current task with the specified exit code.
    /// This function will never return.
    pub fn exit_current(&mut self, exit_code: i32) -> ! {
        let cpu_id = this_cpu_id();
        let curr = vsched_apis::current(cpu_id);
        debug!("task exit: {}, exit_code={}", curr.id_name(), exit_code);
        assert!(curr.is_running(), "task is not running: {:?}", curr.state());
        assert!(!curr.is_idle());
        if curr.is_init() {
            // Safety: it is called from `current_run_queue::<NoPreemptIrqSave>().exit_current(exit_code)`,
            // which disabled IRQs and preemption.
            unsafe {
                EXITED_TASKS.current_ref_mut_raw().clear();
            }
            axhal::power::system_off();
        } else {
            curr.set_state(TaskState::Exited);

            // Notify the joiner task.
            crate::notify_exit(&curr, exit_code);
            // Safety: it is called from `current_run_queue::<NoPreemptIrqSave>().exit_current(exit_code)`,
            // which disabled IRQs and preemption.
            unsafe {
                // Push current task to the `EXITED_TASKS` list, which will be consumed by the GC task.
                EXITED_TASKS.current_ref_mut_raw().push_back(curr.clone());
                // Wake up the GC task to drop the exited tasks.
                WAIT_FOR_EXIT.current_ref_mut_raw().notify_one(false);
            }

            // Schedule to next task.
            vsched_apis::resched(cpu_id);
        }
        unreachable!("task exited!");
    }

    /// Block the current task, put current task into the wait queue and reschedule.
    /// Mark the state of current task as `Blocked`, set the `in_wait_queue` flag as true.
    /// Note:
    ///     1. The caller must hold the lock of the wait queue.
    ///     2. The caller must ensure that the current task is in the running state.
    ///     3. The caller must ensure that the current task is not the idle task.
    ///     4. The lock of the wait queue will be released explicitly after current task is pushed into it.
    pub fn blocked_resched(&mut self, mut wq_guard: WaitQueueGuard) {
        let cpu_id = this_cpu_id();
        let curr = vsched_apis::current(cpu_id);
        assert!(curr.is_running());
        assert!(!curr.is_idle());
        // we must not block current task with preemption disabled.
        // Current expected preempt count is 2.
        // 1 for `NoPreemptIrqSave`, 1 for wait queue's `SpinNoIrq`.
        #[cfg(feature = "preempt")]
        assert!(curr.can_preempt(2));

        // Mark the task as blocked, this has to be done before adding it to the wait queue
        // while holding the lock of the wait queue.
        curr.set_state(TaskState::Blocked);
        curr.set_in_wait_queue(true);

        wq_guard.push_back(curr.clone());
        // Drop the lock of wait queue explictly.
        drop(wq_guard);

        // Current task's state has been changed to `Blocked` and added to the wait queue.
        // Note that the state may have been set as `Ready` in `unblock_task()`,
        // see `unblock_task()` for details.

        debug!("task block: {}", curr.id_name());
        vsched_apis::resched(cpu_id);
        vsched_apis::clear_prev_task_on_cpu(this_cpu_id());
    }

    #[cfg(feature = "irq")]
    pub fn sleep_until(&mut self, deadline: axhal::time::TimeValue) {
        let cpu_id = this_cpu_id();
        let curr = vsched_apis::current(cpu_id);
        debug!("task sleep: {}, deadline={:?}", curr.id_name(), deadline);
        assert!(curr.is_running());
        assert!(!curr.is_idle());

        let now = axhal::time::wall_time();
        if now < deadline {
            crate::timers::set_alarm_wakeup(deadline, curr.clone());
            curr.set_state(TaskState::Blocked);
            vsched_apis::resched(cpu_id);
            vsched_apis::clear_prev_task_on_cpu(this_cpu_id());
        }
    }

    pub fn set_current_priority(&mut self, prio: isize) -> bool {
        vsched_apis::set_priority(prio, this_cpu_id())
    }
}

fn gc_entry() {
    loop {
        // Drop all exited tasks and recycle resources.
        let n = EXITED_TASKS.with_current(|exited_tasks| exited_tasks.len());
        for _ in 0..n {
            // Do not do the slow drops in the critical section.
            let task = EXITED_TASKS.with_current(|exited_tasks| exited_tasks.pop_front());
            if let Some(task) = task {
                let arc_task = task.into_arc();
                if Arc::strong_count(&arc_task) == 1 {
                    // If I'm the last holder of the task, drop it immediately.
                    drop(ManuallyDrop::into_inner(arc_task));
                } else {
                    // Otherwise (e.g, `switch_to` is not compeleted, held by the
                    // joiner, etc), push it back and wait for them to drop first.
                    EXITED_TASKS.with_current(|exited_tasks| exited_tasks.push_back(task));
                }
            }
        }
        // Note: we cannot block current task with preemption disabled,
        // use `current_ref_raw` to get the `WAIT_FOR_EXIT`'s reference here to avoid the use of `NoPreemptGuard`.
        // Since gc task is pinned to the current CPU, there is no affection if the gc task is preempted during the process.
        unsafe { WAIT_FOR_EXIT.current_ref_raw() }.wait();
    }
}

/// The task routine for migrating the current task to the correct CPU.
///
/// It calls `select_run_queue` to get the correct run queue for the task, and
/// then puts the task to the scheduler of target run queue.
#[cfg(feature = "smp")]
pub(crate) fn migrate_entry(migrated_task: TaskRef) {
    current_guard::<kernel_guard::NoPreemptIrqSave>().migrate_entry(migrated_task);
}

#[cfg(feature = "preempt")]
#[unsafe(no_mangle)]
fn current_check_preempt_pending() {
    use kernel_guard::NoPreemptIrqSave;
    let curr = crate::current();
    if curr.need_resched() && curr.can_preempt(0) {
        // Note: if we want to print log msg during `preempt_resched`, we have to
        // disable preemption here, because the axlog may cause preemption.
        let mut rq = current_guard::<NoPreemptIrqSave>();
        if curr.need_resched() {
            rq.preempt_resched()
        }
    }
}

use crate::mem::VSCHED_MAP;
use base_task::{PerCPU, TaskInner, percpu_size_4k_aligned};

pub(crate) fn init() {
    let vsched_map = crate::mem::map_vsched().unwrap();
    VSCHED_MAP.init_once(vsched_map);
    let cpu_id = axhal::percpu::this_cpu_id();
    crate::set_cpu_id(cpu_id);
    let main_task = Task::new_init("main".into());
    let idle_task = Task::new(|| crate::run_idle(), "idle".into(), config::TASK_STACK_SIZE);
    idle_task.set_cpumask(AxCpuMask::one_shot(cpu_id));
    // Put the subsequent execution into the `main` task.
    vsched_apis::init_vsched(cpu_id, idle_task, main_task);
    let gc_task = Task::new(gc_entry, "gc".into(), config::TASK_STACK_SIZE);
    gc_task.set_cpumask(AxCpuMask::one_shot(cpu_id));
    vsched_apis::spawn(cpu_id, gc_task);

    let percpu = VSCHED_MAP.get().unwrap().get_data_pa_size().0;
    let percpu =
        axhal::mem::phys_to_virt(percpu + (percpu_size_4k_aligned::<TaskInner>() * cpu_id))
            .as_ptr_of::<PerCPU>();
    unsafe {
        axhal::percpu::set_current_task_ptr((*percpu).current_task.get());
    }
}

pub(crate) fn init_secondary() {
    let cpu_id = axhal::percpu::this_cpu_id();
    crate::set_cpu_id(cpu_id);
    let idle_task = Task::new_init("idle".into());
    // Put the subsequent execution into the `idle` task.
    vsched_apis::init_vsched(cpu_id, idle_task.clone(), idle_task);

    let percpu = VSCHED_MAP.get().unwrap().get_data_pa_size().0;
    let percpu =
        axhal::mem::phys_to_virt(percpu + (percpu_size_4k_aligned::<TaskInner>() * cpu_id))
            .as_ptr_of::<PerCPU>();
    unsafe {
        axhal::percpu::set_current_task_ptr((*percpu).current_task.get());
    }
}
/// The `YieldFuture` used when yielding the current task and reschedule.
/// When polling this future, the current task will be put into the run queue
/// with `Ready` state and reschedule to the next task on the run queue.
///
/// The polling operation is as the same as the
/// `current_run_queue::<NoPreemptIrqSave>().yield_current()` function.
///
/// SAFETY:
/// Due to this future is constructed with `current_run_queue::<NoPreemptIrqSave>()`,
/// the operation about manipulating the RunQueue and the switching to next task is
/// safe(The `IRQ` and `Preempt` are disabled).
pub(crate) struct YieldFuture<G: BaseGuard> {
    _current_guard: CurrentGuard<G>,
    flag: bool,
}

impl<G: BaseGuard> YieldFuture<G> {
    pub(crate) fn new() -> Self {
        Self {
            _current_guard: current_guard::<G>(),
            flag: false,
        }
    }
}

impl<G: BaseGuard> Unpin for YieldFuture<G> {}

impl<G: BaseGuard> Future for YieldFuture<G> {
    type Output = ();
    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        if !self.flag {
            self.flag = !self.flag;
            let cpu_id = this_cpu_id();
            let curr = vsched_apis::current(cpu_id);
            trace!("task yield: {}", curr.id_name());
            assert!(curr.is_running());

            if vsched_apis::yield_f(cpu_id) {
                Poll::Pending
            } else {
                Poll::Ready(())
            }
        } else {
            Poll::Ready(())
        }
    }
}

/// Due not manually release the `current_run_queue.state`,
/// otherwise it will cause double release.
impl<G: BaseGuard> Drop for YieldFuture<G> {
    fn drop(&mut self) {}
}

/// The `ExitFuture` used when exiting the current task
/// with the specified exit code, which is always return `Poll::Pending`.
///
/// The polling operation is as the same as the
/// `current_run_queue::<NoPreemptIrqSave>().exit_current()` function.
///
/// SAFETY: as the same as the `YieldFuture`. However, It wrap the `CurrentRunQueueRef`
/// with `ManuallyDrop`, otherwise the `IRQ` and `Preempt` state of other
/// tasks(maybe `main` or `gc` task) which recycle the exited task(which used this future)
/// will be error due to automatically drop the `CurrentRunQueueRef.
/// The `CurrentRunQueueRef` should never be drop.
pub(crate) struct ExitFuture<G: BaseGuard> {
    _current_guard: core::mem::ManuallyDrop<CurrentGuard<G>>,
    exit_code: i32,
}

impl<G: BaseGuard> ExitFuture<G> {
    pub(crate) fn new(exit_code: i32) -> Self {
        Self {
            _current_guard: core::mem::ManuallyDrop::new(current_guard::<G>()),
            exit_code,
        }
    }
}

impl<G: BaseGuard> Unpin for ExitFuture<G> {}

impl<G: BaseGuard> Future for ExitFuture<G> {
    type Output = ();
    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        let exit_code = self.exit_code;
        let cpu_id = this_cpu_id();
        let curr = vsched_apis::current(cpu_id);
        debug!("task exit: {}, exit_code={}", curr.id_name(), exit_code);
        assert!(curr.is_running(), "task is not running: {:?}", curr.state());
        assert!(!curr.is_idle());
        curr.set_state(TaskState::Exited);

        // Notify the joiner task.
        crate::notify_exit(&curr, exit_code);

        // Safety: it is called from `current_run_queue::<NoPreemptIrqSave>().exit_current(exit_code)`,
        // which disabled IRQs and preemption.
        unsafe {
            // Push current task to the `EXITED_TASKS` list, which will be consumed by the GC task.
            EXITED_TASKS.current_ref_mut_raw().push_back(curr.clone());
            // Wake up the GC task to drop the exited tasks.
            WAIT_FOR_EXIT.current_ref_mut_raw().notify_one(false);
        }

        assert!(vsched_apis::resched_f(cpu_id));
        Poll::Pending
    }
}

#[cfg(feature = "irq")]
pub(crate) struct SleepUntilFuture<G: BaseGuard> {
    _current_guard: CurrentGuard<G>,
    deadline: axhal::time::TimeValue,
    flag: bool,
}

#[cfg(feature = "irq")]
impl<G: BaseGuard> SleepUntilFuture<G> {
    pub fn new(deadline: axhal::time::TimeValue) -> Self {
        Self {
            _current_guard: current_guard::<G>(),
            deadline,
            flag: false,
        }
    }
}

#[cfg(feature = "irq")]
impl<G: BaseGuard> Unpin for SleepUntilFuture<G> {}

#[cfg(feature = "irq")]
impl<G: BaseGuard> Future for SleepUntilFuture<G> {
    type Output = ();
    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        if !self.flag {
            self.flag = !self.flag;
            let deadline = self.deadline;
            let cpu_id = this_cpu_id();
            let curr = vsched_apis::current(cpu_id);
            debug!("task sleep: {}, deadline={:?}", curr.id_name(), deadline);
            assert!(curr.is_running());
            assert!(!curr.is_idle());

            let now = axhal::time::wall_time();
            if now < deadline {
                crate::timers::set_alarm_wakeup(deadline, curr.clone());
                curr.set_state(TaskState::Blocked);
                assert!(vsched_apis::resched_f(cpu_id));
                Poll::Pending
            } else {
                Poll::Ready(())
            }
        } else {
            Poll::Ready(())
        }
    }
}

#[cfg(feature = "irq")]
impl<G: BaseGuard> Drop for SleepUntilFuture<G> {
    fn drop(&mut self) {}
}

/// The `BlockedReschedFuture` used when blocking the current task.
///
/// When polling this future, current task will be put into the wait queue and reschedule,
/// the state of current task will be marked as `Blocked`, set the `in_wait_queue` flag as true.
/// Note:
///     1. When polling this future, the wait queue is locked.
///     2. When polling this future, the current task is in the running state.
///     3. When polling this future, the current task is not the idle task.
///     4. The lock of the wait queue will be released explicitly after current task is pushed into it.
///
/// SAFETY:
/// as the same as the `YieldFuture`. Due to the `WaitQueueGuard` is not implemented
/// the `Send` trait, this future must hold the reference about the `WaitQueue` instead
/// of the `WaitQueueGuard`.
pub(crate) struct BlockedReschedFuture<'a, G: BaseGuard> {
    _current_guard: CurrentGuard<G>,
    wq: &'a WaitQueue,
    flag: bool,
}

impl<'a, G: BaseGuard> BlockedReschedFuture<'a, G> {
    pub fn new(_current_guard: CurrentGuard<G>, wq: &'a WaitQueue) -> Self {
        Self {
            _current_guard,
            wq,
            flag: false,
        }
    }
}

impl<'a, G: BaseGuard> Unpin for BlockedReschedFuture<'a, G> {}

impl<'a, G: BaseGuard> Future for BlockedReschedFuture<'a, G> {
    type Output = ();
    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        if !self.flag {
            self.flag = !self.flag;
            let mut wq_guard = self.wq.queue.lock();
            let cpu_id = this_cpu_id();
            let curr = vsched_apis::current(cpu_id);
            assert!(curr.is_running());
            assert!(!curr.is_idle());
            // we must not block current task with preemption disabled.
            // Current expected preempt count is 2.
            // 1 for `NoPreemptIrqSave`, 1 for wait queue's `SpinNoIrq`.
            #[cfg(feature = "preempt")]
            assert!(curr.can_preempt(2));

            // Mark the task as blocked, this has to be done before adding it to the wait queue
            // while holding the lock of the wait queue.
            curr.set_state(TaskState::Blocked);
            curr.set_in_wait_queue(true);

            wq_guard.push_back(curr.clone());
            // Drop the lock of wait queue explictly.
            drop(wq_guard);

            // Current task's state has been changed to `Blocked` and added to the wait queue.
            // Note that the state may have been set as `Ready` in `unblock_task()`,
            // see `unblock_task()` for details.

            debug!("task block: {}", curr.id_name());
            assert!(vsched_apis::resched_f(cpu_id));
            Poll::Pending
        } else {
            Poll::Ready(())
        }
    }
}

impl<'a, G: BaseGuard> Drop for BlockedReschedFuture<'a, G> {
    fn drop(&mut self) {}
}
