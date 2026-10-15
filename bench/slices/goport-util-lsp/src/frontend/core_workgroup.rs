//! Go `internal/core/workgroup.go`.
//!
//! PORT: work groups in the language service run over dispatch-thread state
//! (`Rc`, `RefCell`), so they run serially (PORTING "Go runtime";
//! `project/dirty/interfaces.rs`, decision 1). `new_work_group` always makes
//! the single-threaded group. The trait has a lifetime so queued functions
//! can borrow the caller's locals, as Go closures do.

use crate::frontend::prelude::*;
use std::cell::Cell;
use std::collections::VecDeque;
use std::sync::mpsc::{Receiver, SyncSender, TrySendError};

// Go: core/workgroup.go:11 WorkGroup
pub trait WorkGroup<'a> {
    // Queue queues a function to run. It may be invoked immediately, or deferred until RunAndWait.
    // It is not safe to call Queue after RunAndWait has returned.
    fn queue(&self, fn_: Box<dyn FnOnce() + 'a>);

    // RunAndWait runs all queued functions, blocking until they have all completed.
    fn run_and_wait(&self);
}

// Go: core/workgroup.go:20 NewWorkGroup
// PORT: Go makes the parallel group when `singleThreaded` is false. Every
// language-service work group runs on the dispatch thread, so the port
// always makes the single-threaded group. Its functions run last-in
// first-out, as in Go's single-threaded group.

// PORT: Go `defer w.done.Store(true)` in RunAndWait.
struct DoneOnDrop<'g>(&'g Cell<bool>);

impl Drop for DoneOnDrop<'_> {
    fn drop(&mut self) {
        self.0.set(true);
    }
}

// Go: core/workgroup.go:27 parallelWorkGroup
// PORT: never made (see `new_work_group`). Go `wg.Go(fn)` starts a
// goroutine; here the function waits in a first-in first-out list, and
// RunAndWait (Go `wg.Wait()`) runs the list in start order.


// Go: core/workgroup.go:49 singleThreadedWorkGroup
// PORT: `fnsMu` is dropped (one thread).



// Go: core/workgroup.go:92 ThrottleGroup
// ThrottleGroup is like errgroup.Group but with global concurrency limiting via a semaphore.
// PORT: serial. Go `semaphore chan struct{}` is the `sync_channel` pair
// (PORTING "Go runtime"); Go `group *errgroup.Group` is its first error,
// because the functions run on the dispatch thread and `gostd::errgroup`
// runs threads.

// Go: core/workgroup.go:98 NewThrottleGroup
// NewThrottleGroup creates a new ThrottleGroup with the given context and semaphore for concurrency limiting.
// PORT: Go `errgroup.WithContext(ctx)` makes a child context that the
// ThrottleGroup drops unread (`g, _ :=`) and only cancels in Wait. Nothing
// observes it, so the port does not make it.

