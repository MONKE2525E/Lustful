// A persistent worker pool for the compiler's parallel phases (`par_map`).
//
// Workers start on the first parallel phase and serve every later phase. A
// cold compile used to spawn about a hundred threads (one set per phase), and
// each new thread started with a cold allocator heap, so every phase touched
// fresh memory. Reused workers keep their heaps.
//
// One phase runs on the pool at a time. A `par_map` that finds the pool busy
// (a nested call from inside a phase, a second compile on another daemon
// thread, or a stopped pool) uses scoped threads, as every phase did before
// the pool.
//
// `stop` ends every pool thread and keeps the pool stopped while its guard
// lives. tcc's in-memory run forks (src/tcc.rs), and a fork copies only the
// calling thread, so no pool thread may be alive then. The next phase after
// the guard drops starts the pool again.
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Condvar, Mutex, MutexGuard, OnceLock};
use std::thread::JoinHandle;

/// The shared job: every worker that joins runs it once. It must split
/// its own work (`par_map` takes items from an atomic counter). Stored
/// with its lifetime erased; see `run`.
type Job = dyn Fn() + Sync + 'static;

/// The name of every pool thread (also what /proc shows for it).
const THREAD_NAME: &str = "lust-pool";

struct State {
    /// The job of the current phase. Its real lifetime is the `run` call
    /// that set it: `run` returns only after every worker that took it is
    /// done, and late workers cannot take it (`wanted` is 0 by then).
    job: Option<&'static Job>,
    /// Bumped per phase, so a worker joins each phase at most once.
    epoch: u64,
    /// Workers that may still join this phase.
    wanted: usize,
    /// Workers inside the job now.
    running: usize,
    panicked: bool,
    /// A phase or a stop holds the pool.
    busy: bool,
    /// Set by `stop`: workers exit.
    quit: bool,
}

struct Pool {
    state: Mutex<State>,
    /// Workers wait here for a phase or a stop.
    start: Condvar,
    /// `run` waits here for `running` to reach 0.
    done: Condvar,
    /// `stop` waits here for `busy` to clear.
    idle: Condvar,
    workers: usize,
    /// The helper thread that started the workers and joins them when they
    /// quit (see `start_threads`); None while the pool has no threads.
    helper: Mutex<Option<JoinHandle<()>>>,
}

fn lock(p: &Pool) -> MutexGuard<'_, State> {
    p.state.lock().unwrap_or_else(|e| e.into_inner())
}

static POOL: OnceLock<Pool> = OnceLock::new();

/// The process pool: `cores - 1` workers (the caller is the last core).
/// Its threads start with the first phase (`start_threads`).
fn pool() -> &'static Pool {
    POOL.get_or_init(|| Pool {
        state: Mutex::new(State { job: None, epoch: 0, wanted: 0, running: 0, panicked: false, busy: false, quit: false }),
        start: Condvar::new(),
        done: Condvar::new(),
        idle: Condvar::new(),
        workers: std::thread::available_parallelism().map_or(4, |n| n.get()).saturating_sub(1),
        helper: Mutex::new(None),
    })
}

/// Starts the pool's threads when it has none. Called with the pool held
/// (`busy`), so no other thread starts or stops them at the same time. One
/// helper thread starts the workers, so a phase does not wait for every
/// thread start: its caller begins at once, and workers join the phase as
/// they come up. The helper then works as the last worker, and when the
/// workers quit it joins them, so joining the helper joins them all. A
/// thread that fails to start only leaves the phase fewer workers.
fn start_threads(p: &'static Pool) {
    let mut helper = p.helper.lock().unwrap_or_else(|e| e.into_inner());
    if helper.is_some() || p.workers == 0 {
        return;
    }
    let workers = p.workers;
    *helper = std::thread::Builder::new()
        .name(THREAD_NAME.into())
        .spawn(move || {
            let others: Vec<JoinHandle<()>> = (1..workers)
                .filter_map(|_| std::thread::Builder::new().name(THREAD_NAME.into()).spawn(move || worker(p)).ok())
                .collect();
            worker(p);
            for h in others {
                let _ = h.join();
            }
        })
        .ok();
}

/// One pool thread: joins each phase it sees while the phase wants
/// workers, and returns at a stop.
fn worker(p: &'static Pool) {
    #[cfg(test)]
    let _live = tests::Live::new();
    let mut seen = 0u64;
    loop {
        let job = {
            let mut st = lock(p);
            loop {
                if st.quit {
                    return;
                }
                if st.epoch != seen && st.wanted > 0 {
                    break;
                }
                // A phase that needs no more workers counts as seen.
                seen = st.epoch;
                st = p.start.wait(st).unwrap_or_else(|e| e.into_inner());
            }
            seen = st.epoch;
            st.wanted -= 1;
            st.running += 1;
            st.job.expect("a phase in progress has a job")
        };
        let ok = catch_unwind(AssertUnwindSafe(job)).is_ok();
        let mut st = lock(p);
        st.running -= 1;
        st.panicked |= !ok;
        if st.running == 0 {
            p.done.notify_all();
        }
    }
}

/// Releases the pool held by a phase (`run`) or a stop.
fn release(p: &Pool) {
    lock(p).busy = false;
    p.idle.notify_all();
}

/// Ends a phase, also when the caller's own share of the job unwinds:
/// no more workers may join, and the borrowed job outlives every worker
/// that took it. `panicked` holds the phase's worker panic flag, read
/// before the pool is free for the next phase.
struct EndPhase {
    p: &'static Pool,
    panicked: bool,
}

impl EndPhase {
    /// Waits until no worker is inside the job. Idempotent.
    fn finish(&mut self) {
        let mut st = lock(self.p);
        st.wanted = 0;
        while st.running > 0 {
            st = self.p.done.wait(st).unwrap_or_else(|e| e.into_inner());
        }
        st.job = None;
        self.panicked |= st.panicked;
    }
}

impl Drop for EndPhase {
    fn drop(&mut self) {
        self.finish();
        release(self.p);
    }
}

/// Runs `job` on this thread and on up to `extra` workers at once, and
/// returns when every run of it has returned. False (nothing ran) when the
/// pool is busy with another phase or stopped.
fn run(extra: usize, job: &(dyn Fn() + Sync)) -> bool {
    let p = pool();
    if p.workers == 0 {
        return false;
    }
    {
        let mut st = lock(p);
        if st.busy {
            return false;
        }
        st.busy = true;
    }
    start_threads(p);
    // SAFETY: only the lifetime is erased. Workers reach `job` only through
    // `State::job` while `wanted` lets them join, and `EndPhase` (which runs
    // before this function returns or unwinds) sets `wanted` to 0 and waits
    // until no worker is inside the job, then clears it. So no use of the
    // reference outlives this call, and `job` is `Sync` for shared use.
    let job_static: &'static Job = unsafe { std::mem::transmute::<&(dyn Fn() + Sync), &'static Job>(job) };
    {
        let mut st = lock(p);
        st.job = Some(job_static);
        st.epoch += 1;
        st.wanted = extra.min(p.workers);
        st.running = 0;
        st.panicked = false;
    }
    p.start.notify_all();
    let mut end = EndPhase { p, panicked: false };
    job();
    end.finish();
    let panicked = end.panicked;
    drop(end);
    if panicked {
        panic!("a parallel compiler task panicked");
    }
    true
}

/// Holds the pool stopped: no pool thread is alive while this lives, and
/// every `par_map` meanwhile uses scoped threads. Dropping it lets the next
/// phase start the pool again.
pub struct Stopped {
    p: &'static Pool,
}

impl Drop for Stopped {
    fn drop(&mut self) {
        release(self.p);
    }
}

/// Stops the pool: waits for a phase in progress (another thread's) to end,
/// tells every pool thread to quit, and joins them all. Call it where the
/// process must run no other compiler thread: tcc's in-memory run calls it
/// before its fork. Never call it from inside a `par_map` task.
pub fn stop() -> Stopped {
    let p = pool();
    {
        let mut st = lock(p);
        while st.busy {
            st = p.idle.wait(st).unwrap_or_else(|e| e.into_inner());
        }
        st.busy = true;
        st.quit = true;
    }
    p.start.notify_all();
    let helper = p.helper.lock().unwrap_or_else(|e| e.into_inner()).take();
    if let Some(h) = helper {
        let _ = h.join();
    }
    lock(p).quit = false;
    Stopped { p }
}

/// Runs `f` for each item on all cores (`LUST_THREADS` caps the count).
/// Results keep the input order. Items are taken in small batches from
/// one atomic counter, so uneven items still spread over every thread.
pub fn par_map<T: Sync, R: Send>(items: &[T], f: impl Fn(&T) -> R + Sync) -> Vec<R> {
    let cores = std::thread::available_parallelism().map_or(4, |n| n.get());
    let n = std::env::var("LUST_THREADS").ok().and_then(|v| v.parse().ok()).unwrap_or(cores).min(items.len().max(1));
    if n <= 1 {
        return items.iter().map(f).collect();
    }
    let next = AtomicUsize::new(0);
    // Batches amortize the atomic counter, but stay small enough to keep every thread busy.
    let batch = (items.len() / (n * 8)).clamp(1, 16);
    let take = || {
        let mut out = Vec::new();
        loop {
            let start = next.fetch_add(batch, Ordering::Relaxed);
            if start >= items.len() {
                break;
            }
            let end = (start + batch).min(items.len());
            out.extend(items[start..end].iter().enumerate().map(|(k, item)| (start + k, f(item))));
        }
        out
    };
    let parts: Mutex<Vec<Vec<(usize, R)>>> = Mutex::new(Vec::new());
    let job = || {
        let out = take();
        parts.lock().unwrap_or_else(|e| e.into_inner()).push(out);
    };
    let chunks: Vec<Vec<(usize, R)>> = if run(n - 1, &job) {
        parts.into_inner().unwrap_or_else(|e| e.into_inner())
    } else {
        std::thread::scope(|s| {
            let handles: Vec<_> = (0..n).map(|_| s.spawn(take)).collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        })
    };
    let mut all: Vec<Option<R>> = (0..items.len()).map(|_| None).collect();
    for chunk in chunks {
        for (i, r) in chunk {
            all[i] = Some(r);
        }
    }
    all.into_iter().map(|r| r.unwrap()).collect()
}

#[cfg(test)]
mod tests {
    use super::{THREAD_NAME, par_map, stop};
    use std::sync::atomic::{AtomicUsize, Ordering};

    /// Pool threads inside `worker` now: each counts itself while it runs.
    static LIVE: AtomicUsize = AtomicUsize::new(0);

    pub(super) struct Live;

    impl Live {
        pub(super) fn new() -> Live {
            LIVE.fetch_add(1, Ordering::SeqCst);
            Live
        }
    }

    impl Drop for Live {
        fn drop(&mut self) {
            LIVE.fetch_sub(1, Ordering::SeqCst);
        }
    }

    /// Results come back in input order through the pool, a nested call
    /// (which finds the pool busy) still runs every item, and the pool
    /// serves the next phase after both.
    #[test]
    fn par_map_order_nesting_and_reuse() {
        let items: Vec<u64> = (0..1000).collect();
        let out = par_map(&items, |&i| par_map(&[i, i + 1], |&j| j * 2).iter().sum::<u64>());
        assert_eq!(out, items.iter().map(|&i| 4 * i + 2).collect::<Vec<_>>());
        let again = par_map(&items, |&i| i + 1);
        assert_eq!(again, (1..=1000).collect::<Vec<_>>());
    }

    /// A panic in a task reaches the caller, and the pool still works after it.
    #[test]
    fn par_map_panic_reaches_caller() {
        let items: Vec<u32> = (0..64).collect();
        let r = std::panic::catch_unwind(|| par_map(&items, |&i| if i == 40 { panic!("task 40") } else { i }));
        assert!(r.is_err());
        assert_eq!(par_map(&items, |&i| i * 3)[63], 189);
    }

    /// The live threads of this process with the pool's thread name.
    fn pool_threads() -> usize {
        std::fs::read_dir("/proc/self/task")
            .map(|d| {
                d.filter_map(|e| e.ok())
                    .filter(|e| std::fs::read_to_string(e.path().join("comm")).is_ok_and(|c| c.trim_end() == THREAD_NAME))
                    .count()
            })
            .unwrap_or(0)
    }

    /// `stop` leaves no pool thread alive while its guard lives (what tcc's
    /// in-memory fork needs): when it returns, every pool thread has left
    /// its loop and been joined, and the OS lists none soon after. A phase
    /// meanwhile still runs every item on scoped threads, and after the
    /// guard drops the pool starts again.
    #[test]
    fn stop_joins_every_pool_thread() {
        if std::thread::available_parallelism().map_or(1, |n| n.get()) < 2 || !std::path::Path::new("/proc/self/task").exists() {
            return;
        }
        let items: Vec<u64> = (0..4096).collect();
        let slow = |&i: &u64| -> u64 { (0..2000u64).fold(i, |a, k| a.wrapping_mul(31).wrapping_add(k)) };
        let want: Vec<u64> = items.iter().map(slow).collect();
        let secs = |n| std::time::Duration::from_secs(n);
        // Phases until pool threads are up (other tests may hold the pool
        // for a while, and a new thread takes its name as it starts).
        let t0 = std::time::Instant::now();
        while pool_threads() == 0 && t0.elapsed() < secs(5) {
            assert_eq!(par_map(&items, slow), want);
        }
        assert!(pool_threads() > 0, "the pool has threads before the stop");
        let stopped = stop();
        assert_eq!(LIVE.load(Ordering::SeqCst), 0, "a pool thread runs after stop returned");
        // A thread can stay listed for a moment after its join returns.
        let t0 = std::time::Instant::now();
        while pool_threads() > 0 && t0.elapsed() < secs(2) {
            std::thread::yield_now();
        }
        assert_eq!(pool_threads(), 0, "pool threads alive after stop");
        assert_eq!(par_map(&items, slow), want);
        assert_eq!(pool_threads(), 0, "a stopped pool must not start threads");
        assert_eq!(LIVE.load(Ordering::SeqCst), 0);
        drop(stopped);
        let t0 = std::time::Instant::now();
        while pool_threads() == 0 && t0.elapsed() < secs(5) {
            assert_eq!(par_map(&items, slow), want);
        }
        assert!(pool_threads() > 0, "the pool starts again after the guard drops");
    }
}
