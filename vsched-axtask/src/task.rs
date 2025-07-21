use crate::exit_f;
use crate::wait_queue::WaitQueue;
use alloc::boxed::Box;
use alloc::string::String;
use alloc::sync::{Arc, Weak};
use axhal::percpu::this_cpu_id;
use core::cell::UnsafeCell;
use core::ptr::NonNull;
#[cfg(feature = "irq")]
use core::sync::atomic::AtomicU64;
#[cfg(feature = "preempt")]
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use core::sync::atomic::{AtomicBool, AtomicI32};

use base_task::{BaseTask, BaseTaskRef, TaskInner, TaskStack, TaskState, WeakBaseTaskRef};

pub use base_task::TaskExtRef;

/// Task extended data.
pub struct TaskExt {
    name: String,
    entry: Option<*mut dyn FnOnce()>,
    /// Mark whether the task is in the wait queue.
    in_wait_queue: AtomicBool,
    /// A ticket ID used to identify the timer event.
    /// Set by `set_timer_ticket()` when creating a timer event in `set_alarm_wakeup()`,
    /// expired by setting it as zero in `timer_ticket_expired()`, which is called by `cancel_events()`.
    #[cfg(feature = "irq")]
    timer_ticket_id: AtomicU64,

    #[cfg(feature = "preempt")]
    preempt_disable_count: AtomicUsize,
    exit_code: AtomicI32,
    wait_for_exit: WaitQueue,
    /// The future of coroutine task.
    pub future: UnsafeCell<Option<core::pin::Pin<Box<dyn Future<Output = ()> + Send + 'static>>>>,
}

pub struct Task;

impl Task {
    pub fn new<F>(entry: F, name: String, stack_size: usize) -> BaseTaskRef
    where
        F: FnOnce() + Send + 'static,
    {
        let mut t = TaskInner::new();
        t.init_task_ext(TaskExt::new(entry, name));
        unsafe {
            *t.kernel_stack() = Some(TaskStack::alloc(stack_size));
        }
        let kstack_top = t.kernel_stack_top().unwrap();
        t.ctx_mut().init(task_entry as usize, kstack_top);
        let arc_task = Arc::new(BaseTask::new(t));
        let task_raw_ptr = Arc::into_raw(arc_task);
        BaseTaskRef::new(
            NonNull::new(task_raw_ptr as _).unwrap(),
            task_clone,
            task_weak_clone,
            task_drop,
            task_strong_count,
        )
    }

    pub fn new_f<F>(future: F, name: String) -> BaseTaskRef
    where
        F: Future + Send + 'static,
    {
        let mut t = TaskInner::new();
        t.set_alloc_stack_fn(alloc_stack_for_coroutine as usize);
        t.set_coroutine_schedule(coroutine_schedule as usize);
        t.init_task_ext(TaskExt::new_f(future, name));
        let arc_task = Arc::new(BaseTask::new(t));
        let task_raw_ptr = Arc::into_raw(arc_task);
        BaseTaskRef::new(
            NonNull::new(task_raw_ptr as _).unwrap(),
            task_clone,
            task_weak_clone,
            task_drop,
            task_strong_count,
        )
    }

    pub fn new_init(name: String) -> BaseTaskRef {
        let mut t = TaskInner::new();
        t.set_init(true);
        t.set_on_cpu(true);
        if name == "idle" {
            t.set_idle(true);
        }
        t.set_state(TaskState::Running);
        t.init_task_ext(TaskExt::new_init(name));
        let arc_task = Arc::new(BaseTask::new(t));
        let task_raw_ptr = Arc::into_raw(arc_task);
        BaseTaskRef::new(
            NonNull::new(task_raw_ptr as _).unwrap(),
            task_clone,
            task_weak_clone,
            task_drop,
            task_strong_count,
        )
    }
}

/// The function about the `TaskInner`
pub trait TaskTraits {
    /// Get the id_name about the `TaskInner`
    fn id_name(&self) -> alloc::string::String;

    fn join(&self) -> Option<i32>;

    fn join_f(&self) -> impl Future<Output = Option<i32>>;
}

impl TaskTraits for TaskInner {
    fn id_name(&self) -> alloc::string::String {
        alloc::format!("Task({}, {:?})", self.id().as_u64(), self.task_ext().name)
    }

    fn join(&self) -> Option<i32> {
        self.task_ext()
            .wait_for_exit
            .wait_until(|| self.state() == TaskState::Exited);
        Some(self.task_ext().exit_code.load(Ordering::Acquire))
    }

    fn join_f(&self) -> impl Future<Output = Option<i32>> {
        async {
            self.task_ext()
                .wait_for_exit
                .wait_until_f(|| self.state() == TaskState::Exited)
                .await;
            Some(self.task_ext().exit_code.load(Ordering::Acquire))
        }
    }
}

unsafe impl Send for TaskExt {}
unsafe impl Sync for TaskExt {}

impl TaskExt {
    /// Gets the name of the task.
    pub fn name(&self) -> &str {
        self.name.as_str()
    }

    #[inline]
    pub(crate) fn in_wait_queue(&self) -> bool {
        self.in_wait_queue.load(Ordering::Acquire)
    }

    #[inline]
    pub(crate) fn set_in_wait_queue(&self, in_wait_queue: bool) {
        self.in_wait_queue.store(in_wait_queue, Ordering::Release);
    }

    /// Returns task's current timer ticket ID.
    #[inline]
    #[cfg(feature = "irq")]
    pub(crate) fn timer_ticket(&self) -> u64 {
        self.timer_ticket_id.load(Ordering::Acquire)
    }

    /// Set the timer ticket ID.
    #[inline]
    #[cfg(feature = "irq")]
    pub(crate) fn set_timer_ticket(&self, timer_ticket_id: u64) {
        // CAN NOT set timer_ticket_id to 0,
        // because 0 is used to indicate the timer event is expired.
        assert!(timer_ticket_id != 0);
        self.timer_ticket_id
            .store(timer_ticket_id, Ordering::Release);
    }

    /// Expire timer ticket ID by setting it to 0,
    /// it can be used to identify one timer event is triggered or expired.
    #[inline]
    #[cfg(feature = "irq")]
    pub(crate) fn timer_ticket_expired(&self) {
        self.timer_ticket_id.store(0, Ordering::Release);
    }

    #[inline]
    #[cfg(feature = "preempt")]
    pub(crate) fn can_preempt(&self, current_disable_count: usize) -> bool {
        self.preempt_disable_count.load(Ordering::Acquire) == current_disable_count
    }

    #[inline]
    #[cfg(feature = "preempt")]
    pub(crate) fn disable_preempt(&self) {
        self.preempt_disable_count.fetch_add(1, Ordering::Release);
    }

    #[inline]
    #[cfg(feature = "preempt")]
    pub(crate) fn enable_preempt(&self, resched: bool) {
        if self.preempt_disable_count.fetch_sub(1, Ordering::Release) == 1 && resched {
            // If current task is pending to be preempted, do rescheduling.
            Self::current_check_preempt_pending();
        }
    }

    #[cfg(feature = "preempt")]
    fn current_check_preempt_pending() {
        use kernel_guard::NoPreemptIrqSave;
        let curr = crate::current();
        if curr.need_resched() && curr.task_ext().can_preempt(0) {
            // Note: if we want to print log msg during `preempt_resched`, we have to
            // disable preemption here, because the axlog may cause preemption.

            let mut rq = crate::current_guard::<NoPreemptIrqSave>();
            if curr.need_resched() {
                rq.preempt_resched()
            }
        }
    }

    /// Notify all tasks that join on this task.
    pub fn notify_exit(&self, exit_code: i32) {
        self.exit_code.store(exit_code, Ordering::Release);
        self.wait_for_exit.notify_all(false);
    }

    pub fn new<F>(entry: F, name: String) -> Self
    where
        F: FnOnce() + Send + 'static,
    {
        Self {
            name,
            entry: Some(Box::into_raw(Box::new(entry))),
            in_wait_queue: AtomicBool::new(false),
            exit_code: AtomicI32::new(0),
            wait_for_exit: WaitQueue::new(),
            future: UnsafeCell::new(None),
            #[cfg(feature = "irq")]
            timer_ticket_id: AtomicU64::new(0),
            #[cfg(feature = "preempt")]
            preempt_disable_count: AtomicUsize::new(0),
        }
    }

    pub fn new_f<F>(future: F, name: String) -> Self
    where
        F: Future + Send + 'static,
    {
        Self {
            name,
            entry: None,
            in_wait_queue: AtomicBool::new(false),
            exit_code: AtomicI32::new(0),
            wait_for_exit: WaitQueue::new(),
            future: UnsafeCell::new(Some(Box::pin(async {
                future.await;
                exit_f(0).await;
            }))),
            #[cfg(feature = "irq")]
            timer_ticket_id: AtomicU64::new(0),
            #[cfg(feature = "preempt")]
            preempt_disable_count: AtomicUsize::new(0),
        }
    }

    pub fn new_init(name: String) -> Self {
        Self {
            name,
            entry: None,
            in_wait_queue: AtomicBool::new(false),
            exit_code: AtomicI32::new(0),
            wait_for_exit: WaitQueue::new(),
            future: UnsafeCell::new(None),
            #[cfg(feature = "irq")]
            timer_ticket_id: AtomicU64::new(0),
            #[cfg(feature = "preempt")]
            preempt_disable_count: AtomicUsize::new(0),
        }
    }
}

base_task::def_task_ext!(TaskExt);

pub(crate) extern "C" fn task_clone(raw_ptr: *const BaseTask) {
    unsafe { Arc::increment_strong_count(raw_ptr) };
}

pub(crate) extern "C" fn task_drop(raw_ptr: *const BaseTask) {
    unsafe { Arc::decrement_strong_count(raw_ptr) };
}

pub(crate) extern "C" fn task_strong_count(raw_ptr: *const BaseTask) -> usize {
    let _arc_task = unsafe { core::mem::ManuallyDrop::new(Arc::from_raw(raw_ptr)) };
    let count = Arc::strong_count(&_arc_task);
    count
}

pub extern "C" fn task_drop_weak(raw_ptr: *const BaseTask) {
    let weak_task = unsafe { Weak::from_raw(raw_ptr) };
    let arc_task = weak_task.upgrade().unwrap();
    drop(arc_task);
    drop(weak_task);
}

pub(crate) extern "C" fn task_weak_clone(raw_ptr: *const BaseTask) -> WeakBaseTaskRef {
    let _arc_task = unsafe { core::mem::ManuallyDrop::new(Arc::from_raw(raw_ptr)) };
    let weak_task_ptr = Arc::downgrade(&_arc_task).into_raw() as _;
    WeakBaseTaskRef::new(NonNull::new(weak_task_ptr).unwrap(), task_drop_weak)
}

extern "C" fn task_entry() -> ! {
    vsched_apis::clear_prev_task_on_cpu(this_cpu_id());
    let curr = vsched_apis::current(this_cpu_id());
    #[cfg(feature = "irq")]
    axhal::asm::enable_irqs();
    if let Some(entry) = curr.task_ext().entry {
        unsafe { Box::from_raw(entry)() };
    }
    crate::exit(0);
}

#[percpu::def_percpu]
static COROUTINE_STACK_POOL: alloc::vec::Vec<TaskStack> = alloc::vec::Vec::new();

/// Alloc a stack for running a coroutine.
/// If the `COROUTINE_STACK_POOL` is empty,
/// it will alloc a new stack on the allocator.
fn alloc_stack_for_coroutine() -> TaskStack {
    unsafe {
        COROUTINE_STACK_POOL
            .current_ref_mut_raw()
            .pop()
            .unwrap_or_else(|| TaskStack::alloc(axconfig::TASK_STACK_SIZE))
    }
}

/// Recycle the stack after the coroutine running to a certain stage.
fn recycle_stack_of_coroutine(kstack: TaskStack) {
    unsafe {
        COROUTINE_STACK_POOL.current_ref_mut_raw().push(kstack);
    }
}

/// The function about coroutine scheduling.
pub(crate) extern "C" fn coroutine_schedule() {
    use core::task::{Context, Waker};
    loop {
        vsched_apis::clear_prev_task_on_cpu(this_cpu_id());
        #[cfg(feature = "irq")]
        axhal::asm::enable_irqs();
        let waker = Waker::noop();
        let mut cx = Context::from_waker(waker);
        let curr = vsched_apis::current(this_cpu_id());
        let fut = unsafe {
            curr.task_ext()
                .future
                .as_mut_unchecked()
                .as_mut()
                .expect("The task should be a coroutine")
        };
        let _res = fut.as_mut().poll(&mut cx);
        assert!(!curr.is_running(), "{} is not running", curr.id_name());
        let prev_task = curr;
        // pick the kstack of prev_task
        let kstack = unsafe { &mut *prev_task.kernel_stack() }
            .take()
            .expect("The kernel stack should be taken out after running.");
        let next_task = vsched_apis::current(this_cpu_id());
        let next_kstack = unsafe { &mut *next_task.kernel_stack() };
        if next_kstack.is_none() && !next_task.is_init() && !next_task.is_idle() {
            // Pass the `kstack` to the next coroutine task.
            *next_kstack = Some(kstack);
        } else {
            unsafe {
                let prev_ctx_ptr = prev_task.ctx_mut_ptr();
                let next_ctx_ptr = next_task.ctx_mut_ptr();
                recycle_stack_of_coroutine(kstack);
                (*prev_ctx_ptr).switch_to(&*next_ctx_ptr);
                panic!("Should never reach here.");
            }
        }
    }
}
