use crate::this_cpu_id;
use alloc::boxed::Box;
use alloc::string::String;
use alloc::sync::Arc;
use base_task::AxTask;
use base_task::TaskRef;
use base_task::{TaskInner, TaskStack, TaskState};

pub struct Task;

impl Task {
    pub fn new<F>(entry: F, name: String, stack_size: usize) -> TaskRef
    where
        F: FnOnce() + Send + 'static,
    {
        let t = TaskInner::new(entry, task_entry as usize, name, stack_size);
        let arc_task = Arc::new(AxTask::new(t));
        TaskRef::new(Arc::into_raw(arc_task))
    }

    pub fn new_f<F>(future: F, name: String) -> TaskRef
    where
        F: Future<Output = ()> + Send + 'static,
    {
        let mut t = TaskInner::new_f(
            async {
                future.await;
                crate::exit_f(0).await
            },
            name,
        );
        t.set_alloc_stack_fn(alloc_stack_for_coroutine as usize);
        t.set_coroutine_schedule(coroutine_schedule as usize);
        let arc_task = Arc::new(AxTask::new(t));
        TaskRef::new(Arc::into_raw(arc_task))
    }

    pub fn new_init(name: String) -> TaskRef {
        let t = TaskInner::new_init(name);
        t.set_state(TaskState::Running);
        let arc_task = Arc::new(AxTask::new(t));
        TaskRef::new(Arc::into_raw(arc_task))
    }
}

extern "C" fn task_entry() -> ! {
    vsched_apis::clear_prev_task_on_cpu(this_cpu_id());
    let curr = crate::current();
    #[cfg(feature = "irq")]
    axhal::asm::enable_irqs();
    if let Some(entry) = curr.entry() {
        unsafe { Box::from_raw(*entry)() };
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
        let curr = crate::current();
        let fut = curr
            .future()
            .as_mut()
            .expect("The task should be a coroutine");
        let _res = fut.as_mut().poll(&mut cx);
        assert!(!curr.is_running(), "{} is not running", curr.id_name());
        let prev_task = curr;
        // pick the kstack of prev_task
        let kstack = unsafe { &mut *prev_task.kernel_stack() }
            .take()
            .expect("The kernel stack should be taken out after running.");
        let next_task = crate::current();
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

/// A wrapper of [`TaskRef`] as the current task.
///
/// It won't change the reference count of the task when created or dropped.
pub struct CurrentTask(TaskRef);

impl CurrentTask {
    pub(crate) fn try_get() -> Option<Self> {
        let ptr: *const TaskRef = axhal::percpu::current_task_ptr();
        if !ptr.is_null() {
            Some(Self(unsafe { ptr.read_volatile() }))
        } else {
            None
        }
    }

    pub(crate) fn get() -> Self {
        Self::try_get().expect("current task is uninitialized")
    }

    /// Converts [`CurrentTask`] to [`AxTaskRef`].
    pub fn as_task_ref(&self) -> &TaskRef {
        &self.0
    }

    #[cfg(any(feature = "irq", feature = "smp"))]
    pub(crate) fn clone(&self) -> TaskRef {
        self.0.clone()
    }

    pub(crate) fn ptr_eq(&self, other: &TaskRef) -> bool {
        self.0.ptr_eq(other)
    }
}

impl core::ops::Deref for CurrentTask {
    type Target = TaskInner;
    fn deref(&self) -> &Self::Target {
        self.0.deref()
    }
}
