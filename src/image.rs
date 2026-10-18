// Persistent front end for one-shot builds (rel-front): the session a daemon
// keeps, saved to a file when a build ends and mapped back when the next one
// starts, so a build with no warm daemon (a CI release job) takes the
// daemon's incremental paths (body patch, item patch, header deltas, kept
// program, read sets, unit objects) after a process exit.
//
// Turned on by `LUST_FRONT_STATE=<dir>` (Linux only). The state is a heap
// image, not a serialized form: every heap block of the session stays where
// it was, so the restored session is the same memory the last process had.
//
//   1. lust-core re-executes itself once (`reexec`) with address space
//      randomization off, so the binary and its libraries load at the same
//      addresses as in the run that wrote the image (vtables, fn pointers,
//      and `&'static` data in the heap stay valid), and with
//      `LUST_FRONT_ARENA` naming a fixed base address.
//   2. The global allocator (`Alloc`, mimalloc underneath) maps a fixed
//      address range at that base on the first allocation and gives it to
//      mimalloc as the only memory it may use, so every heap block of the
//      process is inside it.
//   3. After the build, `save` writes the image as layers: a base
//      (`front.img`) after a cold build, then one delta per build
//      (`front.d<k>.img`) holding only the restored pages this process
//      wrote (`/proc/self/pagemap`) plus the new arena's live pages; after
//      MAX_DELTAS deltas, or deltas whose data passes half the base, a new
//      base, which copies the untouched pages from the old layer files.
//      Zero pages (freed blocks among them) are holes in every layer. Each
//      layer has a header (format, compiler build, address anchors, the
//      `Roots` pointer, the next arena base, its parent layer), a region
//      table, then pages. When the system's libzstd loads (and unless
//      `LUST_FRONT_ZSTD=0`) a layer is written packed (`pack`): its raw form in 8 MB
//      zstd sections, which the next run reads in one pass and unpacks in
//      parallel into a memfd (`unpack`): on a CI disk, page faults on a
//      raw tsgo chain (13.2 GB) cost a fresh merge 12.8 s, and the chain
//      packs to 1.1 GB. Arena pages hold the live blocks mimalloc
//      reports (`mi_heap_visit_blocks`), with the bytes of free blocks
//      written as zeros; pages with no live block are left out. The
//      process-wide tables the session's spans index into
//      (`diag::GlobalTables`) and the stamp counters ride in `Roots`.
//      With `LUST_FRONT_SAVE=background` a forked child writes them while
//      the build answers and exits (`save_background`); a release build
//      forks it before its cc step (`driver::defer_cc`), so the image is
//      written while clang runs. Every image
//      process holds the state directory's lock (`lock`) from before its
//      load to its exit, a background save's child to the save's end: a
//      build waits for the save before it, and a release waits for its
//      own (`flock <dir>/lock true`) before it caches the directory.
//   4. The next run maps the layers back at their addresses, newest pages
//      last (`load`: MAP_PRIVATE, so pages load lazily and no layer file is
//      ever written), and uses the restored session. A free of a restored
//      block zeroes it and never reuses it; new blocks come from a fresh
//      arena above the restored regions.
//
// Any doubt is a cold build that writes a fresh image: a missing or
// foreign image (format, build, anchors), a region that cannot map, a
// session key that differs from the request's, a live block outside the
// arena at save time.
//
// `unsafe` here is waived in docs/ARCH.md section 9.6 (front image).
use std::alloc::{GlobalAlloc, Layout};
use std::ffi::{c_char, c_int, c_void};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicI32, AtomicU8, AtomicUsize, Ordering};

/// The state directory variable (`LUST_FRONT_STATE=<dir>`).
pub const STATE_ENV: &str = "LUST_FRONT_STATE";
/// Set for the re-executed process: the arena base address, in hex.
const ARENA_ENV: &str = "LUST_FRONT_ARENA";
/// `LUST_FRONT_SAVE=background`: the build answers and exits first, a
/// forked child saves (`save_background`).
pub const SAVE_ENV: &str = "LUST_FRONT_SAVE";
/// The image file in the state directory.
const IMAGE_FILE: &str = "front.img";
/// The state directory's lock file (`lock`).
const LOCK_FILE: &str = "lock";
/// A background save's result line, in the state directory.
const SAVE_LOG: &str = "save.log";
/// `LUST_FRONT_COMPACT=1`: this process rebuilds the image cold and writes it as a new base
/// (`main::image_run`): a run a background save started (`compact_exec`), or a command of its
/// own, such as a CI job after the release job. `LUST_FRONT_COMPACT=defer`: a save never starts
/// a compaction; it leaves `COMPACT_DUE` when one is due.
const COMPACT_ENV: &str = "LUST_FRONT_COMPACT";
/// The state lock's descriptor, which a compacting process inherits (`compact_exec`).
const LOCK_FD_ENV: &str = "LUST_FRONT_LOCK_FD";
/// The build process a compacting process waits for before it starts (`compact_exec`).
const WAIT_PID_ENV: &str = "LUST_FRONT_WAIT_PID";
/// Left by a compaction that did not finish: later saves write a plain base (`compaction_due`).
const NO_COMPACT: &str = "nocompact";
/// Left by a save that wrote a plain base while a compaction was due (`compaction_due`), so a job
/// of its own can run one (`LUST_FRONT_COMPACT=1`); the next cold base removes it.
const COMPACT_DUE: &str = "compact-due";
/// Image format. Bump on any change to the header or to what `Roots` holds.
const MAGIC: &[u8; 8] = b"LUSTFIM3";
/// A packed layer (`pack`): the raw (`MAGIC`) layer in zstd sections.
const MAGIC_PACKED: &[u8; 8] = b"LUSTFIZ2";
/// Saves write packed layers when libzstd loads; `LUST_FRONT_ZSTD=0` keeps
/// them raw.
const PACK_ENV: &str = "LUST_FRONT_ZSTD";
/// Raw bytes per packed section; sections pack and unpack in parallel.
const SECTION: usize = 8 << 20;
const RTLD_NOW: c_int = 2;
const MFD_CLOEXEC: std::ffi::c_uint = 1;
/// Arena bases come from this window, one generation after another:
/// 16 TiB to 80 TiB, below where Linux puts a non-randomized binary
/// (0x5555_5555_4000) and its mmap area.
const WINDOW_LO: usize = 0x1000_0000_0000;
const WINDOW_HI: usize = 0x5000_0000_0000;
/// Address space one process's arena reserves (MAP_NORESERVE: only
/// touched pages cost memory). A tsgo build peaks under 10 GB of heap.
const ARENA_SIZE: usize = 128 << 30;
/// One mimalloc arena's share of it.
const ARENA_PART: usize = 8 << 30;
const PAGE: usize = 4096;
/// Header bytes before the region table.
const HEADER: usize = 8 + 64 + 8 * 4 + 8 * 7;
/// Deltas on one base before a save writes a new base.
const MAX_DELTAS: usize = 16;
/// The mapped span (every restored run plus the new arena's pages) past
/// which a save drops the image instead (the next build is cold).
const MAX_SPAN: usize = 128 << 30;

unsafe extern "C" {
    fn getenv(name: *const c_char) -> *const c_char;
    fn mmap(addr: *mut c_void, len: usize, prot: c_int, flags: c_int, fd: c_int, off: i64) -> *mut c_void;
    fn munmap(addr: *mut c_void, len: usize) -> c_int;
    fn personality(persona: u64) -> c_int;
    fn writev(fd: c_int, iov: *const IoVec, cnt: c_int) -> isize;
    fn lseek(fd: c_int, off: i64, whence: c_int) -> i64;
    fn pread(fd: c_int, buf: *mut c_void, count: usize, off: i64) -> isize;
    fn pwrite(fd: c_int, buf: *const c_void, count: usize, off: i64) -> isize;
    fn copy_file_range(fd_in: c_int, off_in: *mut i64, fd_out: c_int, off_out: *mut i64, len: usize, flags: u32) -> isize;
    fn flock(fd: c_int, op: c_int) -> c_int;
    fn fcntl(fd: c_int, cmd: c_int, arg: c_int) -> c_int;
    fn fork() -> c_int;
    fn setsid() -> c_int;
    fn dup2(old: c_int, new: c_int) -> c_int;
    fn _exit(code: c_int) -> !;
    fn mi_manage_os_memory_ex(
        start: *mut c_void,
        size: usize,
        is_committed: bool,
        is_pinned: bool,
        is_zero: bool,
        numa_node: c_int,
        exclusive: bool,
        arena_id: *mut *mut c_void,
    ) -> bool;
    fn mi_option_set(option: c_int, value: std::ffi::c_long);
    fn mi_heap_visit_blocks(heap: *mut c_void, visit_blocks: bool, visitor: Visitor, arg: *mut c_void) -> bool;
    fn dlopen(file: *const c_char, mode: c_int) -> *mut c_void;
    fn dlsym(handle: *mut c_void, name: *const c_char) -> *mut c_void;
    fn memfd_create(name: *const c_char, flags: std::ffi::c_uint) -> c_int;
}

const PROT_RW: c_int = 0x1 | 0x2;
const MAP_PRIVATE: c_int = 0x02;
const MAP_FIXED: c_int = 0x10;
const MAP_ANONYMOUS: c_int = 0x20;
const MAP_NORESERVE: c_int = 0x4000;
const MAP_FIXED_NOREPLACE: c_int = 0x10_0000;
const ADDR_NO_RANDOMIZE: u64 = 0x0040000;
const LOCK_EX: c_int = 2;
const F_SETFD: c_int = 2;
const FD_CLOEXEC: c_int = 1;
const EINTR: i32 = 4;
/// `mi_option_disallow_os_alloc` in mimalloc 3.3 (libmimalloc-sys 0.1.49).
const MI_OPTION_DISALLOW_OS_ALLOC: c_int = 17;

/// 0: not started, 1: plain process, 2: arena process, 3: starting.
static MODE: AtomicU8 = AtomicU8::new(0);
/// This process's arena: [ARENA_LO, ARENA_LO + ARENA_SIZE).
static ARENA_LO: AtomicUsize = AtomicUsize::new(0);
/// The restored regions' span: frees there zero the block instead.
static OLD_LO: AtomicUsize = AtomicUsize::new(0);
static OLD_LEN: AtomicUsize = AtomicUsize::new(0);
/// Bytes of restored blocks freed in this process (dead space a save keeps).
static OLD_FREED: AtomicUsize = AtomicUsize::new(0);

/// The global allocator: mimalloc, plus the fixed arena in image mode and
/// the never-reused restored blocks after a `load`.
pub struct Alloc;

#[inline]
fn restored(p: *mut u8) -> bool {
    (p as usize).wrapping_sub(OLD_LO.load(Ordering::Relaxed)) < OLD_LEN.load(Ordering::Relaxed)
}

/// Runs on the first allocation (on the main thread, before any other
/// thread exists): in a re-executed image process, maps the arena and
/// makes it mimalloc's only memory.
#[cold]
fn start() {
    if MODE.compare_exchange(0, 3, Ordering::AcqRel, Ordering::Acquire).is_err() {
        while MODE.load(Ordering::Acquire) == 3 {
            std::hint::spin_loop();
        }
        return;
    }
    let mut mode = 1;
    // SAFETY: getenv reads the environment block; the name is NUL-terminated.
    let v = unsafe { getenv(c"LUST_FRONT_ARENA".as_ptr()) };
    if let Some(base) = (!v.is_null()).then(|| parse_hex(v)).flatten().filter(|b| valid_base(*b)) {
        // SAFETY: a fixed mapping that may not replace anything (NOREPLACE);
        // the result is checked before use.
        let p = unsafe {
            mmap(base as *mut c_void, ARENA_SIZE, PROT_RW, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE | MAP_FIXED_NOREPLACE, -1, 0)
        };
        if p as usize == base {
            // SAFETY: the range is ours, mapped read-write and zero above.
            // Option 17 makes mimalloc take memory from these arenas only.
            unsafe {
                // Arenas of ARENA_PART bytes: mimalloc 3.3 refuses the
                // 16 GiB sub-arenas it would split a bigger range into
                // (their metadata needs 521 slices, it allows 512).
                let parts = (0..ARENA_SIZE)
                    .step_by(ARENA_PART)
                    .take_while(|&off| {
                        let mut id = std::ptr::null_mut();
                        mi_manage_os_memory_ex((base + off) as *mut c_void, ARENA_PART, true, false, true, -1, false, &mut id)
                    })
                    .count();
                if parts == ARENA_SIZE / ARENA_PART {
                    mi_option_set(MI_OPTION_DISALLOW_OS_ALLOC, 1);
                    ARENA_LO.store(base, Ordering::Relaxed);
                    mode = 2;
                } else if parts == 0 {
                    munmap(p, ARENA_SIZE);
                }
                // Else mimalloc owns some parts: they stay mapped, and
                // this process builds without an image.
            }
        } else if p as isize != -1 {
            // SAFETY: an unexpected address (an old kernel ignores NOREPLACE): give it back.
            unsafe { munmap(p, ARENA_SIZE) };
        }
    }
    MODE.store(mode, Ordering::Release);
}

/// A hex address from a NUL-terminated string, without allocating.
fn parse_hex(mut s: *const c_char) -> Option<usize> {
    let mut v: usize = 0;
    let mut any = false;
    loop {
        // SAFETY: `s` walks a NUL-terminated string from getenv.
        let c = unsafe { *s } as u8;
        if c == 0 {
            return any.then_some(v);
        }
        v = v.checked_mul(16)?.checked_add((c as char).to_digit(16)? as usize)?;
        any = true;
        // SAFETY: not past the NUL checked above.
        s = unsafe { s.add(1) };
    }
}

fn valid_base(b: usize) -> bool {
    b >= WINDOW_LO && b.checked_add(ARENA_SIZE).is_some_and(|e| e <= WINDOW_HI) && b % (1 << 30) == 0
}

// SAFETY: every path forwards to mimalloc's GlobalAlloc, except frees and
// reallocs of restored blocks, which mimalloc never handed out: those
// copy out (realloc) and zero the old bytes, and never free them.
unsafe impl GlobalAlloc for Alloc {
    #[inline]
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        if MODE.load(Ordering::Relaxed) == 0 {
            start();
        }
        // SAFETY: the caller's layout contract passes through.
        unsafe { mimalloc::MiMalloc.alloc(l) }
    }
    #[inline]
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        if MODE.load(Ordering::Relaxed) == 0 {
            start();
        }
        // SAFETY: as `alloc`.
        unsafe { mimalloc::MiMalloc.alloc_zeroed(l) }
    }
    #[inline]
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        if restored(p) {
            // SAFETY: the caller owned the block's `l.size()` bytes.
            unsafe { std::ptr::write_bytes(p, 0, l.size()) };
            OLD_FREED.fetch_add(l.size(), Ordering::Relaxed);
            return;
        }
        // SAFETY: as `alloc`.
        unsafe { mimalloc::MiMalloc.dealloc(p, l) }
    }
    #[inline]
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 {
        if restored(p) {
            // SAFETY: `n` is non-zero and fits the alignment (the caller's
            // contract); the old block holds `l.size()` bytes.
            unsafe {
                let q = self.alloc(Layout::from_size_align_unchecked(n, l.align()));
                if !q.is_null() {
                    std::ptr::copy_nonoverlapping(p, q, l.size().min(n));
                    std::ptr::write_bytes(p, 0, l.size());
                    OLD_FREED.fetch_add(l.size(), Ordering::Relaxed);
                }
                return q;
            }
        }
        // SAFETY: as `alloc`.
        unsafe { mimalloc::MiMalloc.realloc(p, l, n) }
    }
}

/// The state directory, when image mode is asked for (Linux only).
pub fn state_dir() -> Option<PathBuf> {
    if !cfg!(target_os = "linux") {
        return None;
    }
    std::env::var_os(STATE_ENV).filter(|v| !v.is_empty()).map(PathBuf::from)
}

/// True in the re-executed process whose heap is the fixed arena.
pub fn arena_on() -> bool {
    MODE.load(Ordering::Relaxed) == 2
}

/// Re-executes this lust-core with randomization off and an arena base
/// above the current image's regions. Returns only when it cannot (no
/// `personality`, exec failed, the window is used up): the caller then
/// builds without an image.
pub fn reexec(dir: &Path) -> String {
    // The re-executed process itself, when its arena did not start: never
    // again (that would loop).
    if REEXECED.load(Ordering::Relaxed) {
        return "arena setup failed".into();
    }
    // A background save of the build before this one writes the header
    // read next: wait for its lock (`lock`), then let it go; the new
    // process takes it again before its load.
    // A compacting process holds the lock already (`compact_exec`) and builds cold.
    let compact = compact_mode();
    if !compact && let Ok(f) = std::fs::File::open(dir.join(LOCK_FILE)) {
        use std::os::fd::AsRawFd;
        flock_wait(f.as_raw_fd());
    }
    // Above the image's regions, or the window's start when the image is
    // unusable or the window is used up (`load` then refuses the image).
    // Anchors are checked by `load` in the new process: this one runs
    // with randomization on, so its addresses differ anyway.
    let top = if compact { None } else { read_chain(dir).ok().and_then(|mut c| c.pop()) };
    let base = match top {
        Some(h) if h.build == build_id() && valid_base(h.next_base as usize) => h.next_base as usize,
        _ => WINDOW_LO,
    };
    // SAFETY: personality(0xffffffff) only reads the persona; the second call sets one flag.
    let persona = unsafe { personality(0xffff_ffff) };
    if persona < 0 || unsafe { personality(persona as u64 | ADDR_NO_RANDOMIZE) } < 0 {
        return "personality(ADDR_NO_RANDOMIZE) failed".into();
    }
    use std::os::unix::process::CommandExt;
    let mut cmd = std::process::Command::new("/proc/self/exe");
    cmd.args(std::env::args_os().skip(1)).env(ARENA_ENV, format!("{base:x}"));
    // The disk cache (unit objects, slot manifest, build script records,
    // base libraries) belongs with the image: one directory to keep.
    if std::env::var_os("LUST_CACHE_DIR").is_none_or(|v| v.is_empty()) {
        cmd.env("LUST_CACHE_DIR", dir.join("cache"));
    }
    let err = cmd.exec();
    format!("re-exec failed: {err}")
}

/// Set in a process that `reexec` started.
static REEXECED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Start of main, single-threaded. In a process `reexec` started (arena
/// or not), children (cargo, tcc, user programs) get randomization back
/// and no arena variable.
pub fn process_start() {
    if std::env::var_os(ARENA_ENV).is_none() {
        return;
    }
    REEXECED.store(true, Ordering::Relaxed);
    // SAFETY: as in `reexec`; clearing the flag affects only later execs.
    // remove_var: no other thread exists yet.
    unsafe {
        let p = personality(0xffff_ffff);
        if p >= 0 {
            personality(p as u64 & !ADDR_NO_RANDOMIZE);
        }
        std::env::remove_var(ARENA_ENV);
    }
}

/// What an image carries besides the session: the process-wide state the
/// session's data points into or orders against.
pub struct Roots {
    /// One session per crate selection, as a daemon keeps them.
    pub sessions: Vec<Box<crate::driver::Session>>,
    pub tables: crate::diag::GlobalTables,
    pub stamps: crate::driver::Stamps,
    /// The Cargo graphs the builds loaded (`cargo::take_graph_cache`).
    pub graphs: crate::resolve::cargo::GraphCache,
}

/// Address anchors: a function and a static of this binary and a libc
/// function. All three move when the binary, its load address, or libc's
/// does, and the heap's code and data pointers would then dangle.
fn anchors() -> [u64; 4] {
    let exe_len = std::fs::metadata("/proc/self/exe").map_or(0, |m| m.len());
    [start as *const () as u64, &MODE as *const AtomicU8 as u64, getenv as *const () as u64, exe_len]
}

struct Header {
    build: [u8; 64],
    anchors: [u64; 4],
    root: u64,
    next_base: u64,
    generation: u64,
    /// Bytes of live data the layer holds (compaction compares them).
    live: u64,
    /// This layer's id, and its parent's (0 for a base).
    id: u64,
    parent: u64,
    /// (address, length, file offset), all page-aligned. A packed layer's
    /// offsets are in its raw form.
    regions: Vec<(u64, u64, u64)>,
    /// A packed layer's raw length and sections (file offset, packed
    /// length, `section_check`).
    packed: Option<(u64, Vec<(u64, u64, u64)>)>,
}

impl Header {
    fn compatible(&self) -> bool {
        self.build == build_id() && self.anchors == anchors()
    }
    fn bytes(&self) -> Vec<u8> {
        let mut b = Vec::with_capacity(HEADER + self.regions.len() * 24);
        b.extend_from_slice(MAGIC);
        b.extend_from_slice(&self.build);
        for a in self.anchors {
            b.extend_from_slice(&a.to_le_bytes());
        }
        for v in [self.root, self.next_base, self.generation, self.live, self.id, self.parent, self.regions.len() as u64] {
            b.extend_from_slice(&v.to_le_bytes());
        }
        for &(a, l, o) in &self.regions {
            for v in [a, l, o] {
                b.extend_from_slice(&v.to_le_bytes());
            }
        }
        b
    }
}

fn build_id() -> [u8; 64] {
    let mut id = [0u8; 64];
    let h = env!("LUST_BUILD_HASH").as_bytes();
    id[..h.len().min(64)].copy_from_slice(&h[..h.len().min(64)]);
    id
}

/// The file of layer `k`: the base (0), or delta `k` on top of layer `k - 1`.
fn layer_path(dir: &Path, k: usize) -> PathBuf {
    if k == 0 { dir.join(IMAGE_FILE) } else { dir.join(format!("front.d{k}.img")) }
}

fn read_header(path: &Path) -> Result<Header, String> {
    use std::io::Read;
    let mut f = std::fs::File::open(path).map_err(|e| format!("no image: {e}"))?;
    let mut head = vec![0u8; HEADER];
    f.read_exact(&mut head).map_err(|_| "short image".to_string())?;
    let word = |b: &[u8], i: usize| u64::from_le_bytes(b[i..i + 8].try_into().unwrap());
    if &head[..8] == MAGIC_PACKED {
        // A packed layer (`pack`): raw length, section count and the raw
        // header's length, the raw header, then the section table.
        let (raw_len, n, head_len) = (word(&head, 8), word(&head, 16), word(&head, 24));
        if n > 1 << 24 || head_len > 1 << 30 || (head_len as usize) < HEADER {
            return Err("packed image header".into());
        }
        // The first HEADER bytes are read; the rest of the head follows.
        let mut all = head.clone();
        all.resize(32 + head_len as usize + n as usize * 24, 0);
        f.read_exact(&mut all[HEADER..]).map_err(|_| "short packed image".to_string())?;
        let file_len = f.metadata().map_err(|e| format!("image: {e}"))?.len();
        let inner = &all[32..32 + head_len as usize];
        let mut h = parse_header(&inner[..HEADER], &inner[HEADER..], raw_len)?;
        let table = &all[32 + head_len as usize..];
        let sections: Vec<(u64, u64, u64)> = table.chunks_exact(24).map(|c| (word(c, 0), word(c, 8), word(c, 16))).collect();
        if sections.len() != raw_len.div_ceil(SECTION as u64) as usize || sections.iter().any(|&(o, l, _)| o.checked_add(l).is_none_or(|e| e > file_len)) {
            return Err("packed image section table".into());
        }
        h.packed = Some((raw_len, sections));
        return Ok(h);
    }
    if &head[..8] != MAGIC {
        return Err("image format".into());
    }
    let n = word(&head, 104 + 8 * 6);
    if n > 1 << 24 {
        return Err("image region count".into());
    }
    let mut table = vec![0u8; n as usize * 24];
    f.read_exact(&mut table).map_err(|_| "short image table".to_string())?;
    let len = f.metadata().map_err(|e| format!("image: {e}"))?.len();
    parse_header(&head, &table, len)
}

/// A raw layer's header and region table, its regions checked against the
/// layer's (raw) length.
fn parse_header(head: &[u8], table: &[u8], len: u64) -> Result<Header, String> {
    let word = |b: &[u8], i: usize| u64::from_le_bytes(b[i..i + 8].try_into().unwrap());
    if head.len() < HEADER || &head[..8] != MAGIC {
        return Err("image format".into());
    }
    let mut build = [0u8; 64];
    build.copy_from_slice(&head[8..72]);
    let anchors = [word(head, 72), word(head, 80), word(head, 88), word(head, 96)];
    let [root, next_base, generation, live, id, parent, n] = std::array::from_fn(|i| word(head, 104 + 8 * i));
    if table.len() as u64 != n.saturating_mul(24) {
        return Err("image region table".into());
    }
    let regions: Vec<(u64, u64, u64)> = table.chunks_exact(24).map(|c| (word(c, 0), word(c, 8), word(c, 16))).collect();
    if regions
        .iter()
        .any(|&(a, l, o)| a % PAGE as u64 != 0 || l % PAGE as u64 != 0 || o % PAGE as u64 != 0 || o.checked_add(l).is_none_or(|e| e > len))
    {
        return Err("image region table".into());
    }
    Ok(Header { build, anchors, root, next_base, generation, live, id, parent, regions, packed: None })
}

/// The system's libzstd, opened on first use with dlopen (no build-time
/// link): packed layers (`pack`, `unpack`). None when it is missing; saves
/// then write raw layers, and a packed image does not load.
struct Zstd {
    compress: unsafe extern "C" fn(*mut c_void, usize, *const c_void, usize, c_int) -> usize,
    decompress: unsafe extern "C" fn(*mut c_void, usize, *const c_void, usize) -> usize,
    bound: unsafe extern "C" fn(usize) -> usize,
    is_error: unsafe extern "C" fn(usize) -> std::ffi::c_uint,
}

fn zstd() -> Option<&'static Zstd> {
    static Z: std::sync::OnceLock<Option<Zstd>> = std::sync::OnceLock::new();
    Z.get_or_init(|| {
        // SAFETY: dlopen and dlsym by name; each symbol is libzstd's stable
        // API (zstd.h) with exactly the signature it is cast to.
        unsafe {
            let lib = dlopen(c"libzstd.so.1".as_ptr(), RTLD_NOW);
            if lib.is_null() {
                return None;
            }
            let sym = |name: &std::ffi::CStr| dlsym(lib, name.as_ptr());
            let (c, d, b, e) = (sym(c"ZSTD_compress"), sym(c"ZSTD_decompress"), sym(c"ZSTD_compressBound"), sym(c"ZSTD_isError"));
            if c.is_null() || d.is_null() || b.is_null() || e.is_null() {
                return None;
            }
            Some(Zstd {
                compress: std::mem::transmute::<*mut c_void, unsafe extern "C" fn(*mut c_void, usize, *const c_void, usize, c_int) -> usize>(c),
                decompress: std::mem::transmute::<*mut c_void, unsafe extern "C" fn(*mut c_void, usize, *const c_void, usize) -> usize>(d),
                bound: std::mem::transmute::<*mut c_void, unsafe extern "C" fn(usize) -> usize>(b),
                is_error: std::mem::transmute::<*mut c_void, unsafe extern "C" fn(usize) -> std::ffi::c_uint>(e),
            })
        }
    })
    .as_ref()
}

/// The libzstd a save packs with: None when `LUST_FRONT_ZSTD=0` or when
/// libzstd does not load (then `raw_why` says which).
fn packer() -> Option<&'static Zstd> {
    zstd().filter(|_| std::env::var_os(PACK_ENV).is_none_or(|v| v != "0"))
}

/// Why saves stay raw, for the save line (None when they pack).
fn raw_why() -> Option<&'static str> {
    match (std::env::var_os(PACK_ENV).is_some_and(|v| v == "0"), zstd().is_some()) {
        (true, _) => Some("raw (LUST_FRONT_ZSTD=0)"),
        (false, false) => Some("raw (no libzstd)"),
        (false, true) => None,
    }
}

/// A packed section's check: a hash of its packed bytes, so a damaged
/// layer fails to load (a cold build) instead of mapping wrong pages.
fn section_check(b: &[u8]) -> u64 {
    use std::hash::Hasher;
    let mut h = crate::intern::FxHasher::default();
    h.write(b);
    h.write_usize(b.len());
    h.finish()
}

/// The threads that pack or unpack a layer's sections.
fn workers() -> usize {
    std::thread::available_parallelism().map_or(4, |n| n.get()).clamp(1, 16)
}

/// Fills `buf` from `f` at `off` (a hole reads as zeros).
fn read_full_at(f: &std::fs::File, buf: &mut [u8], off: u64) -> bool {
    std::os::unix::fs::FileExt::read_exact_at(f, buf, off).is_ok()
}

/// Writes raw layer `raw` (`len` bytes; `head` is its header and region
/// table) to `out` packed: a short header (`MAGIC_PACKED`, the raw length,
/// the section count, `head`'s length), `head` itself (so the chain reads
/// without unpacking), the section table (file offset, packed length,
/// `section_check`), then the raw form cut into `SECTION`-byte sections,
/// each one zstd frame, packed in parallel. Returns the packed length.
fn pack(raw: &std::fs::File, len: u64, head: &[u8], out: &mut std::fs::File, z: &Zstd) -> Result<u64, String> {
    use std::io::Write;
    let n = (len as usize).div_ceil(SECTION);
    let level: c_int = std::env::var("LUST_FRONT_ZSTD_LEVEL").ok().and_then(|v| v.parse().ok()).unwrap_or(1);
    let parts: Vec<std::sync::Mutex<Option<Vec<u8>>>> = (0..n).map(|_| std::sync::Mutex::new(None)).collect();
    let next = AtomicUsize::new(0);
    let failed = std::sync::atomic::AtomicBool::new(false);
    std::thread::scope(|s| {
        for _ in 0..workers().min(n.max(1)) {
            s.spawn(|| {
                let mut rbuf = vec![0u8; SECTION];
                loop {
                    let k = next.fetch_add(1, Ordering::Relaxed);
                    if k >= n || failed.load(Ordering::Relaxed) {
                        break;
                    }
                    let at = k * SECTION;
                    let rlen = (len as usize - at).min(SECTION);
                    if !read_full_at(raw, &mut rbuf[..rlen], at as u64) {
                        failed.store(true, Ordering::Relaxed);
                        break;
                    }
                    // SAFETY: libzstd's documented contract; both buffers are valid for the lengths passed.
                    let bound = unsafe { (z.bound)(rlen) };
                    let mut cbuf = vec![0u8; bound];
                    let c = unsafe { (z.compress)(cbuf.as_mut_ptr() as *mut c_void, bound, rbuf.as_ptr() as *const c_void, rlen, level) };
                    if unsafe { (z.is_error)(c) } != 0 {
                        failed.store(true, Ordering::Relaxed);
                        break;
                    }
                    cbuf.truncate(c);
                    *parts[k].lock().unwrap_or_else(|e| e.into_inner()) = Some(cbuf);
                }
            });
        }
    });
    if failed.load(Ordering::Relaxed) {
        return Err("image pack failed".into());
    }
    let parts: Vec<Vec<u8>> = parts.into_iter().map(|m| m.into_inner().unwrap_or_else(|e| e.into_inner()).unwrap_or_default()).collect();
    let mut at = (32 + head.len() + n * 24) as u64;
    let mut table = Vec::with_capacity(n * 24);
    for p in &parts {
        for v in [at, p.len() as u64, section_check(p)] {
            table.extend_from_slice(&v.to_le_bytes());
        }
        at += p.len() as u64;
    }
    let mut w = std::io::BufWriter::with_capacity(4 << 20, out);
    let mut top = Vec::with_capacity(32);
    top.extend_from_slice(MAGIC_PACKED);
    for v in [len, n as u64, head.len() as u64] {
        top.extend_from_slice(&v.to_le_bytes());
    }
    let ok = w.write_all(&top).is_ok() && w.write_all(head).is_ok() && w.write_all(&table).is_ok() && parts.iter().all(|p| w.write_all(p).is_ok()) && w.flush().is_ok();
    if !ok {
        return Err("image pack write failed".into());
    }
    Ok(at)
}

/// Packed layer `path` back in its raw form, in a new memfd that the
/// regions then map privately (`load`): the sections unpacked in parallel,
/// each section's zero pages left out, so they stay holes and read as zero.
fn unpack(path: &Path, raw_len: u64, sections: &[(u64, u64, u64)], z: &Zstd) -> Result<std::fs::File, String> {
    use std::os::fd::FromRawFd;
    use std::os::unix::fs::FileExt;
    let src = std::fs::File::open(path).map_err(|e| format!("image: {e}"))?;
    // SAFETY: a new anonymous file; the File below owns its descriptor.
    let fd = unsafe { memfd_create(c"lust-front-layer".as_ptr(), MFD_CLOEXEC) };
    if fd < 0 {
        return Err("memfd_create failed".into());
    }
    // SAFETY: `fd` is a fresh descriptor no one else holds.
    let mem = unsafe { std::fs::File::from_raw_fd(fd) };
    mem.set_len(raw_len).map_err(|e| format!("image memfd: {e}"))?;
    let next = AtomicUsize::new(0);
    let failed = std::sync::atomic::AtomicBool::new(false);
    std::thread::scope(|s| {
        for _ in 0..workers().min(sections.len().max(1)) {
            s.spawn(|| {
                let mut cbuf: Vec<u8> = Vec::new();
                let mut rbuf = vec![0u8; SECTION];
                loop {
                    let k = next.fetch_add(1, Ordering::Relaxed);
                    if k >= sections.len() || failed.load(Ordering::Relaxed) {
                        break;
                    }
                    let (off, clen, check) = sections[k];
                    let at = k * SECTION;
                    let rlen = (raw_len as usize - at).min(SECTION);
                    cbuf.resize(clen as usize, 0);
                    if !read_full_at(&src, &mut cbuf, off) || section_check(&cbuf) != check {
                        failed.store(true, Ordering::Relaxed);
                        break;
                    }
                    // SAFETY: libzstd's documented contract; both buffers are valid for the lengths passed.
                    let d = unsafe { (z.decompress)(rbuf.as_mut_ptr() as *mut c_void, rlen, cbuf.as_ptr() as *const c_void, cbuf.len()) };
                    if unsafe { (z.is_error)(d) } != 0 || d != rlen {
                        failed.store(true, Ordering::Relaxed);
                        break;
                    }
                    // Runs of pages with a nonzero byte; zero pages stay holes.
                    let zero = |q: usize| rbuf[q..(q + PAGE).min(rlen)].chunks(8).all(|c| c.iter().all(|&b| b == 0));
                    let mut q = 0;
                    while q < rlen {
                        if zero(q) {
                            q += PAGE;
                            continue;
                        }
                        let s0 = q;
                        while q < rlen && !zero(q) {
                            q += PAGE;
                        }
                        let e = q.min(rlen);
                        if mem.write_all_at(&rbuf[s0..e], (at + s0) as u64).is_err() {
                            failed.store(true, Ordering::Relaxed);
                            break;
                        }
                    }
                }
            });
        }
    });
    if failed.load(Ordering::Relaxed) {
        return Err(format!("cannot unpack {}", path.display()));
    }
    Ok(mem)
}

/// The layers that make up the image in `dir`: the base, then each delta
/// whose parent is the layer before it (a stale delta ends the chain).
fn read_chain(dir: &Path) -> Result<Vec<Header>, String> {
    let base = read_header(&layer_path(dir, 0))?;
    if base.parent != 0 {
        return Err("image base is a delta".into());
    }
    let mut chain = vec![base];
    while let Ok(h) = read_header(&layer_path(dir, chain.len())) {
        if h.parent != chain.last().map_or(0, |p| p.id) {
            break;
        }
        chain.push(h);
    }
    Ok(chain)
}

/// True when some mapping other than this process's arena lies in the
/// image window (`load` maps layers over it with MAP_FIXED).
fn window_taken(arena: usize) -> bool {
    let maps = std::fs::read_to_string("/proc/self/maps").unwrap_or_default();
    maps.lines().filter_map(|l| l.split_whitespace().next()?.split_once('-')).any(|(s, e)| {
        let (s, e) = (usize::from_str_radix(s, 16).unwrap_or(0), usize::from_str_radix(e, 16).unwrap_or(0));
        s < arena && e > WINDOW_LO
    })
}

/// Maps the image's layers back and returns the top layer's roots, or why
/// not. Call at the start of an image process: the regions lie below this
/// process's arena (`reexec` placed it above them).
pub fn load(dir: &Path) -> Result<Box<Roots>, String> {
    use std::os::fd::AsRawFd;
    if LOADED.get().is_some() {
        return Err("image already loaded".into());
    }
    let chain = read_chain(dir)?;
    if !chain.iter().all(Header::compatible) {
        return Err("image from another lust build".into());
    }
    let arena = ARENA_LO.load(Ordering::Relaxed);
    if chain.iter().flat_map(|h| &h.regions).any(|&(a, l, _)| (a as usize) < WINDOW_LO || (a + l) as usize > arena) {
        return Err("image regions outside the window".into());
    }
    if window_taken(arena) {
        return Err("image window in use".into());
    }
    // A packed layer unpacks into a memfd with its raw form: one read of the
    // file instead of page faults on it (a CI disk serves those slowly).
    let mut files = Vec::with_capacity(chain.len());
    for (k, h) in chain.iter().enumerate() {
        files.push(match &h.packed {
            Some((raw_len, sections)) => unpack(&layer_path(dir, k), *raw_len, sections, zstd().ok_or("a packed image, and no libzstd")?)?,
            None => std::fs::File::open(layer_path(dir, k)).map_err(|e| format!("image: {e}"))?,
        });
    }
    let mut mapped: Vec<(usize, usize)> = Vec::new();
    let unmap_all = |mapped: &[(usize, usize)]| {
        for &(a, l) in mapped {
            // SAFETY: only regions this call mapped; nothing points there yet.
            unsafe { munmap(a as *mut c_void, l) };
        }
    };
    for (k, h) in chain.iter().enumerate() {
        let fd = files[k].as_raw_fd();
        for &(a, l, o) in &h.regions {
            // SAFETY: a private mapping in the image window, which holds
            // only this call's own earlier layers (`window_taken`): a delta
            // page replaces the older page at its address.
            let p = unsafe { mmap(a as *mut c_void, l as usize, PROT_RW, MAP_PRIVATE | MAP_FIXED, fd, o as i64) };
            if p as usize != a as usize {
                unmap_all(&mapped);
                return Err(format!("cannot map image region {a:#x}"));
            }
            mapped.push((a as usize, l as usize));
        }
    }
    // The restored span, as page runs (overlapping layers merged).
    mapped.sort_unstable();
    let mut runs: Vec<(usize, usize)> = Vec::new();
    for (a, l) in mapped {
        match runs.last_mut() {
            Some((_, e)) if a <= *e => *e = (*e).max(a + l),
            _ => runs.push((a, a + l)),
        }
    }
    let mut src: Vec<(usize, usize, usize, u64)> = Vec::new();
    for (k, h) in chain.iter().enumerate() {
        let mut layer: Vec<(usize, usize, usize, u64)> = h.regions.iter().map(|&(a, l, o)| (a as usize, (a + l) as usize, k, o)).collect();
        layer.sort_unstable_by_key(|r| r.0);
        src = overlay(&src, &layer);
    }
    let top = chain.last().expect("a chain has its base");
    OLD_LO.store(runs.first().map_or(0, |r| r.0), Ordering::Relaxed);
    OLD_LEN.store(runs.last().map_or(0, |r| r.1) - runs.first().map_or(0, |r| r.0), Ordering::Relaxed);
    GEN.store(top.generation as usize + 1, Ordering::Relaxed);
    // The deltas' data on disk (their holes cost nothing): past half the
    // base's live bytes, the next save writes a new base.
    let deltas: u64 = files[1..].iter().map(|f| f.metadata().map_or(0, |m| std::os::unix::fs::MetadataExt::blocks(&m) * 512)).sum();
    let packed = chain.iter().filter(|h| h.packed.is_some()).count();
    let _ = LOADED.set(Loaded { runs, src, layers: chain.len(), top_id: top.id, base_live: chain[0].live, delta_bytes: deltas, live: top.live, files, packed });
    // SAFETY: the root was a leaked `Box<Roots>` of a process running this
    // same binary at the same addresses (checked: build id, anchors), and
    // every page it reaches is mapped back above.
    Ok(unsafe { Box::from_raw(top.root as usize as *mut Roots) })
}

/// What `load` mapped, for the next save.
struct Loaded {
    /// The restored page runs (start, end), sorted and disjoint.
    runs: Vec<(usize, usize)>,
    /// Where each restored page came from: (start, end, layer, file
    /// offset of start), sorted and disjoint, the topmost layer's
    /// (`overlay`). A base write copies untouched pages from there.
    src: Vec<(usize, usize, usize, u64)>,
    layers: usize,
    top_id: u64,
    base_live: u64,
    delta_bytes: u64,
    /// The session's live bytes when the top layer was written (estimate).
    live: u64,
    /// Each layer's raw form (the file, or a packed layer's memfd), which
    /// a base write copies untouched pages from.
    files: Vec<std::fs::File>,
    /// How many layers were packed.
    packed: usize,
}

static LOADED: std::sync::OnceLock<Loaded> = std::sync::OnceLock::new();

/// The generation of this process's image (0 = written by a cold build).
static GEN: AtomicUsize = AtomicUsize::new(0);

/// How many images led to this process's session (0: a cold one).
pub fn generation() -> usize {
    GEN.load(Ordering::Relaxed)
}

/// The form of the restored layers, for the build line: `packed`, or why
/// they (and this run's saves) are raw.
pub fn layers_note() -> String {
    match LOADED.get().map(|l| (l.packed, l.layers)) {
        Some((p, n)) if p == n => "packed".into(),
        Some((p, _)) if p > 0 => format!("packed and raw; saves {}", raw_why().map_or("pack", |_| "stay raw")),
        _ => raw_why().map_or_else(|| "raw; saves pack".to_string(), str::to_string),
    }
}

/// The restored runs of this process (none in a cold one).
fn restored_runs() -> &'static [(usize, usize)] {
    LOADED.get().map_or(&[], |l| &l.runs)
}

#[repr(C)]
struct IoVec {
    base: *const u8,
    len: usize,
}

#[repr(C)]
struct HeapArea {
    blocks: *mut u8,
    reserved: usize,
    committed: usize,
    used: usize,
    block_size: usize,
    full_block_size: usize,
    reserved1: *mut u8,
}

type Visitor = extern "C" fn(*const c_void, *const HeapArea, *mut u8, usize, *mut c_void) -> bool;

/// A static zero page source for the gaps between live blocks.
static ZEROS: [u8; 1 << 16] = [0; 1 << 16];

/// The save's state while mimalloc visits blocks. Nothing here allocates:
/// the visit walks the allocator's own structures.
struct Walk {
    lo: usize,
    /// One bit per arena page: holds a live byte.
    pages: *mut u64,
    pass: u8,
    blocks: usize,
    live: usize,
    outside: usize,
    unordered: bool,
    last_end: usize,
    /// Pass 2: the page runs, the current run, and the write position.
    runs: *const (usize, usize),
    n_runs: usize,
    run: usize,
    pos: usize,
    iov: *mut IoVec,
    n_iov: usize,
    fd: c_int,
    failed: bool,
}

const IOV_MAX: usize = 1024;

impl Walk {
    fn push(&mut self, base: *const u8, len: usize) {
        if len == 0 {
            return;
        }
        // SAFETY: `iov` holds IOV_MAX entries (raw mapping in `save`).
        unsafe { *self.iov.add(self.n_iov) = IoVec { base, len } };
        self.n_iov += 1;
        if self.n_iov == IOV_MAX {
            self.flush();
        }
    }
    fn zeros(&mut self, mut len: usize) {
        while len > 0 {
            let n = len.min(ZEROS.len());
            self.push(ZEROS.as_ptr(), n);
            len -= n;
        }
    }
    fn flush(&mut self) {
        let mut i = 0;
        while i < self.n_iov && !self.failed {
            // SAFETY: entries i.. are initialized; each names readable memory
            // (a live block, or ZEROS).
            let w = unsafe { writev(self.fd, self.iov.add(i), (self.n_iov - i).min(IOV_MAX) as c_int) };
            if w <= 0 {
                self.failed = true;
                break;
            }
            let mut w = w as usize;
            while w > 0 {
                // SAFETY: as above.
                let e = unsafe { &mut *self.iov.add(i) };
                if w >= e.len {
                    w -= e.len;
                    i += 1;
                } else {
                    e.base = e.base.wrapping_add(w);
                    e.len -= w;
                    w = 0;
                }
            }
        }
        self.n_iov = 0;
    }
    /// Pass 2: write bytes up to address `a` of the current run as zeros,
    /// moving to the run that holds `a` (finishing runs before it).
    fn advance(&mut self, a: usize) {
        while self.run < self.n_runs {
            // SAFETY: run < n_runs.
            let (s, e) = unsafe { *self.runs.add(self.run) };
            if self.pos < s {
                self.pos = s;
            }
            if a < self.pos {
                // A block pass 1 did not place: the heap changed between
                // the passes. The save fails rather than write a wrong image.
                self.failed = true;
                return;
            }
            if a < e {
                self.zeros(a - self.pos);
                self.pos = a;
                return;
            }
            self.zeros(e - self.pos);
            self.pos = e;
            self.run += 1;
        }
        // Past every run: only the final call may get here.
        if a != usize::MAX {
            self.failed = true;
        }
    }
}

extern "C" fn visit(_heap: *const c_void, _area: *const HeapArea, block: *mut u8, size: usize, arg: *mut c_void) -> bool {
    if block.is_null() || size == 0 {
        return true;
    }
    // SAFETY: `arg` is the `Walk` that `save` passed, alive for the visit.
    let w = unsafe { &mut *(arg as *mut Walk) };
    let a = block as usize;
    if a < w.lo || a + size > w.lo + ARENA_SIZE {
        w.outside += 1;
        return true;
    }
    if a < w.last_end {
        w.unordered = true;
        return false;
    }
    w.last_end = a + size;
    if w.pass == 1 {
        w.blocks += 1;
        w.live += size;
        for p in (a - w.lo) / PAGE..=(a + size - 1 - w.lo) / PAGE {
            // SAFETY: p < ARENA_SIZE / PAGE, the bitmap's size.
            unsafe { *w.pages.add(p / 64) |= 1 << (p % 64) };
        }
    } else {
        w.advance(a);
        if !w.failed {
            w.push(block, size);
            w.pos = a + size;
        }
    }
    !w.failed
}

/// Raw zeroed memory outside the heap (the visit must not allocate).
fn raw(len: usize) -> Option<(*mut u8, usize)> {
    let len = len.div_ceil(PAGE).max(1) * PAGE;
    // SAFETY: a fresh anonymous mapping; checked.
    let p = unsafe { mmap(std::ptr::null_mut(), len, PROT_RW, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0) };
    (p as isize != -1).then_some((p as *mut u8, len))
}

fn unraw((p, len): (*mut u8, usize)) {
    // SAFETY: a mapping `raw` made, unused after this.
    unsafe { munmap(p as *mut c_void, len) };
}

/// Writes `[a, a + len)` (page-aligned, readable) at the file's position,
/// leaving all-zero pages as holes: freed restored blocks were zeroed
/// (`Alloc::dealloc`), so a sparse file keeps the image's disk use near its
/// live bytes, while the pages still map back (as zeros: a live block may
/// hold zeros). One write per run of non-zero pages.
fn write_sparse(file: &mut std::fs::File, a: usize, len: usize) -> bool {
    use std::io::{Seek, SeekFrom, Write};
    // SAFETY: [a, a + len) is readable (a region `load` mapped).
    let bytes = unsafe { std::slice::from_raw_parts(a as *const u8, len) };
    let zero = |p: &[u8]| p.chunks_exact(8).all(|w| w == [0u8; 8]);
    let mut at = 0;
    while at < len {
        let start = at;
        let z = zero(&bytes[at..at + PAGE]);
        while at < len && zero(&bytes[at..at + PAGE]) == z {
            at += PAGE;
        }
        let ok = if z { file.seek(SeekFrom::Current((at - start) as i64)).is_ok() } else { file.write_all(&bytes[start..at]).is_ok() };
        if !ok {
            return false;
        }
    }
    true
}

/// `top`'s intervals over `under`'s, each (start, end, layer, file offset
/// of start), sorted and disjoint: the parts of `under` that `top` covers
/// go (a delta page replaces the older page at its address).
fn overlay(under: &[(usize, usize, usize, u64)], top: &[(usize, usize, usize, u64)]) -> Vec<(usize, usize, usize, u64)> {
    let mut out = Vec::with_capacity(under.len() + 2 * top.len());
    let mut j = 0;
    for &(a, b, k, o) in under {
        while j < top.len() && top[j].1 <= a {
            j += 1;
        }
        let mut x = a;
        let mut jj = j;
        while x < b {
            match top.get(jj) {
                Some(&(ta, tb, _, _)) if ta < b => {
                    if ta > x {
                        out.push((x, ta, k, o + (x - a) as u64));
                    }
                    x = x.max(tb);
                    jj += 1;
                }
                _ => {
                    out.push((x, b, k, o + (x - a) as u64));
                    x = b;
                }
            }
        }
    }
    out.extend_from_slice(top);
    out.sort_unstable_by_key(|r| r.0);
    out
}

/// Writes restored run [a, e) of a new base at file offset `out`: the pages
/// this process wrote from memory (zero pages as holes, `write_sparse_at`),
/// the rest copied from the layer files they came from (`src`, `fds`) with
/// their holes kept (`copy_extents`). An untouched page is never read
/// through its mapping, which would fault it in: a long-lived image maps
/// many times its live bytes. Allocates nothing (it runs between the
/// save's two passes).
fn write_base_run(file: &std::fs::File, out: u64, a: usize, e: usize, modified: &[(usize, usize)], src: &[(usize, usize, usize, u64)], fds: &[c_int]) -> bool {
    use std::os::fd::AsRawFd;
    let fd = file.as_raw_fd();
    let mut mi = modified.partition_point(|m| m.1 <= a);
    let mut si = src.partition_point(|s| s.1 <= a);
    let mut x = a;
    while x < e {
        if let Some(&(ms, me)) = modified.get(mi)
            && ms <= x
        {
            let end = me.min(e);
            if !write_sparse_at(file, out + (x - a) as u64, x, end - x) {
                return false;
            }
            x = end;
            if me <= x {
                mi += 1;
            }
            continue;
        }
        let end = modified.get(mi).map_or(e, |m| m.0).min(e);
        while x < end {
            let Some(&(ss, se, k, so)) = src.get(si) else { return false };
            if se <= x {
                si += 1;
                continue;
            }
            if ss > x || k >= fds.len() {
                return false;
            }
            let stop = se.min(end);
            if !copy_extents(fds[k], so + (x - ss) as u64, fd, out + (x - a) as u64, (stop - x) as u64) {
                return false;
            }
            x = stop;
        }
    }
    true
}

/// `write_sparse` at file offset `out`, with positional writes.
fn write_sparse_at(file: &std::fs::File, out: u64, a: usize, len: usize) -> bool {
    use std::os::unix::fs::FileExt;
    // SAFETY: [a, a + len) holds pages this process wrote: mapped and resident.
    let bytes = unsafe { std::slice::from_raw_parts(a as *const u8, len) };
    let zero = |p: &[u8]| p.chunks_exact(8).all(|w| w == [0u8; 8]);
    let mut at = 0;
    while at < len {
        let start = at;
        let z = zero(&bytes[at..at + PAGE]);
        while at < len && zero(&bytes[at..at + PAGE]) == z {
            at += PAGE;
        }
        if !z && file.write_all_at(&bytes[start..at], out + start as u64).is_err() {
            return false;
        }
    }
    true
}

/// Copies `len` bytes of file `src` at `off` to file `dst` at `out`, data
/// extents only (`SEEK_DATA`, `SEEK_HOLE`): a hole stays a hole. In the
/// kernel (`copy_file_range`), or through a stack buffer where that
/// fails. Allocates nothing.
fn copy_extents(src: c_int, mut off: u64, dst: c_int, mut out: u64, len: u64) -> bool {
    const SEEK_DATA: c_int = 3;
    const SEEK_HOLE: c_int = 4;
    let end = off + len;
    while off < end {
        // SAFETY: lseek on an open fd; copies use explicit offsets.
        let data = unsafe { lseek(src, off as i64, SEEK_DATA) };
        if data < 0 || data as u64 >= end {
            return true;
        }
        out += data as u64 - off;
        off = data as u64;
        // SAFETY: as above.
        let hole = unsafe { lseek(src, off as i64, SEEK_HOLE) };
        let stop = if hole < 0 { end } else { (hole as u64).min(end) };
        while off < stop {
            let (mut i, mut o) = (off as i64, out as i64);
            // SAFETY: two open fds, offsets owned here.
            let n = unsafe { copy_file_range(src, &mut i, dst, &mut o, (stop - off) as usize, 0) };
            let n = if n > 0 { n as u64 } else { copy_slow(src, off, dst, out, stop - off) };
            if n == 0 {
                return false;
            }
            off += n;
            out += n;
        }
    }
    true
}

/// One `pread`/`pwrite` step of `copy_extents` through a stack buffer;
/// the bytes copied, 0 on failure.
fn copy_slow(src: c_int, off: u64, dst: c_int, out: u64, len: u64) -> u64 {
    let mut buf = [0u8; 1 << 16];
    let n = (len as usize).min(buf.len());
    // SAFETY: a stack buffer of at least n bytes; both fds are open.
    let r = unsafe { pread(src, buf.as_mut_ptr() as *mut c_void, n, off as i64) };
    if r <= 0 {
        return 0;
    }
    let mut w = 0usize;
    while w < r as usize {
        // SAFETY: the first r bytes of the buffer, as above.
        let k = unsafe { pwrite(dst, buf.as_ptr().add(w) as *const c_void, r as usize - w, (out + w as u64) as i64) };
        if k <= 0 {
            return 0;
        }
        w += k as usize;
    }
    r as u64
}

/// Pages of the restored runs this process wrote (copy-on-write made them
/// anonymous) or that went to swap: `/proc/self/pagemap` bit 63 present,
/// 62 swapped, 61 file page. Untouched and read-only pages are still the
/// layers' own.
fn modified_runs(runs: &[(usize, usize)]) -> Result<Vec<(usize, usize)>, String> {
    use std::os::unix::fs::FileExt;
    let f = std::fs::File::open("/proc/self/pagemap").map_err(|e| format!("pagemap: {e}"))?;
    let mut out: Vec<(usize, usize)> = Vec::new();
    let mut buf = vec![0u8; 8 << 16];
    for &(a, e) in runs {
        let mut p = a;
        while p < e {
            let n = ((e - p) / PAGE).min(buf.len() / 8);
            f.read_exact_at(&mut buf[..n * 8], (p / PAGE * 8) as u64).map_err(|e| format!("pagemap: {e}"))?;
            for (i, c) in buf[..n * 8].chunks_exact(8).enumerate() {
                let v = u64::from_le_bytes(c.try_into().unwrap());
                let modified = (v >> 63 & 1 == 1 && v >> 61 & 1 == 0) || v >> 62 & 1 == 1;
                if modified {
                    let at = p + i * PAGE;
                    match out.last_mut() {
                        Some((_, end)) if *end == at => *end += PAGE,
                        _ => out.push((at, at + PAGE)),
                    }
                }
            }
            p += n * PAGE;
        }
    }
    Ok(out)
}

/// Set once this process holds the state directory's lock.
static LOCKED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
/// The lock's descriptor (`lock`, `compact_lock`).
static LOCK_FD: AtomicI32 = AtomicI32::new(-1);
/// Set by a run whose saves may compact the image (`allow_compaction`).
static COMPACT_OK: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Takes the state directory's lock for the rest of this process (call it
/// before `load`): one image process per directory at a time, so a build
/// waits for the one before it to end, background save included. The lock
/// belongs to the file's open description, which a forked child shares;
/// it goes when the last process holding it exits. Without it (no
/// directory, no `flock`) the build still goes on.
pub fn lock(dir: &Path) {
    use std::os::fd::IntoRawFd;
    let _ = std::fs::create_dir_all(dir);
    let Ok(f) = std::fs::OpenOptions::new().create(true).append(true).open(dir.join(LOCK_FILE)) else { return };
    // Never closed: the lock lasts to exit. Close-on-exec, so compilers
    // and linkers the build starts do not hold it.
    let fd = f.into_raw_fd();
    if flock_wait(fd) {
        LOCKED.store(true, Ordering::Relaxed);
        LOCK_FD.store(fd, Ordering::Relaxed);
    }
}

/// True in a process that rebuilds the image cold (`COMPACT_ENV`).
pub fn compact_mode() -> bool {
    std::env::var_os(COMPACT_ENV).is_some_and(|v| v == "1")
}

/// The state lock in a compacting process. A run a background save started inherits the save
/// child's descriptor across the exec (`compact_exec`), close-on-exec again so the compilers
/// this run starts do not hold it. A command of its own takes the lock as a build does, after
/// any save that holds it. False when there is no lock: the process then must not touch the
/// state.
pub fn compact_lock(dir: &Path) -> bool {
    let Some(fd) = std::env::var(LOCK_FD_ENV).ok().and_then(|v| v.parse::<c_int>().ok()) else {
        lock(dir);
        return LOCKED.load(Ordering::Relaxed);
    };
    // SAFETY: fcntl on a descriptor of this process.
    if unsafe { fcntl(fd, F_SETFD, FD_CLOEXEC) } < 0 {
        return false;
    }
    LOCK_FD.store(fd, Ordering::Relaxed);
    LOCKED.store(true, Ordering::Relaxed);
    true
}

/// In a compacting process: waits until the build that started its save has exited (its cc
/// step and link run after the fork, `driver::defer_cc`), so the cold rebuild runs after the
/// artifact, not beside clang.
pub fn wait_for_build() {
    let Some(pid) = std::env::var(WAIT_PID_ENV).ok().filter(|p| !p.is_empty()) else { return };
    let proc = std::path::PathBuf::from(format!("/proc/{pid}"));
    let start = std::time::Instant::now();
    while proc.exists() && start.elapsed() < std::time::Duration::from_secs(3600) {
        std::thread::sleep(std::time::Duration::from_millis(50));
    }
}

/// Lets this run's background save compact the image (`compaction_due`): only a run of release
/// driver builds, whose compaction parks and drops every cc step, so it writes no artifact.
pub fn allow_compaction(on: bool) {
    COMPACT_OK.store(on, Ordering::Relaxed);
}

/// Stops compaction for this state directory, with why (a compaction that failed would
/// otherwise run again at every save).
pub fn refuse_compaction(dir: &Path, why: &str) {
    let _ = std::fs::write(dir.join(NO_COMPACT), format!("{why}\n"));
}

/// True when a base is due (`write_image`): too many deltas, or their data passes half the base.
fn base_due(l: &Loaded) -> bool {
    !(l.layers <= MAX_DELTAS && l.delta_bytes < l.base_live / 2)
}

/// True when this save should rebuild the image cold instead of writing a base from this
/// heap: a base is due and the image's restored span passes `LUST_FRONT_COMPACT_RATIO` (default
/// 3 when saves pack, else 1.5; 0 for never) times its live bytes. Restored
/// memory is never reused and a page that holds a live block is kept whole, so a base from
/// this heap keeps every such page (tsgo's 12-merge replay: 8.7, 12.7, 17.0 GB bases for 4.7,
/// 5.2, 5.7 GB live).
fn compaction_due(dir: &Path) -> bool {
    let Some(l) = LOADED.get() else { return false };
    // Packed, a scattered base costs a few seconds to save and restore, so
    // compaction (a cold rebuild) waits for a larger span.
    let ratio = std::env::var("LUST_FRONT_COMPACT_RATIO").ok().and_then(|v| v.parse::<f64>().ok()).unwrap_or(if packer().is_some() { 3.0 } else { 1.5 });
    let span: usize = l.runs.iter().map(|&(a, e)| e - a).sum();
    COMPACT_OK.load(Ordering::Relaxed)
        && ratio > 0.0
        && base_due(l)
        && span as f64 > l.live as f64 * ratio
        && !dir.join(NO_COMPACT).exists()
}

/// Replaces this save child with a fresh run of the same command that rebuilds the image cold
/// and writes it as a new base (`main::image_run` in compact mode). The state lock's descriptor
/// stays open across the exec, so the lock holds until that run ends. Returns only when the
/// exec failed.
fn compact_exec(build_pid: u32) -> String {
    use std::os::unix::process::CommandExt;
    let fd = LOCK_FD.load(Ordering::Relaxed);
    // SAFETY: fcntl on a descriptor of this process.
    if fd < 0 || unsafe { fcntl(fd, F_SETFD, 0) } < 0 {
        return "no state lock descriptor".into();
    }
    let mut cmd = std::process::Command::new("/proc/self/exe");
    cmd.args(std::env::args_os().skip(1))
        .env(COMPACT_ENV, "1")
        .env(LOCK_FD_ENV, fd.to_string())
        .env(WAIT_PID_ENV, build_pid.to_string())
        .env_remove(SAVE_ENV)
        .env_remove(ARENA_ENV);
    format!("compaction exec failed: {}", cmd.exec())
}

/// Takes the lock on open file `fd`, waiting for its holder. False when
/// `flock` fails.
fn flock_wait(fd: c_int) -> bool {
    loop {
        // SAFETY: `fd` is an open file.
        if unsafe { flock(fd, LOCK_EX) } == 0 {
            return true;
        }
        if std::io::Error::last_os_error().raw_os_error() != Some(EINTR) {
            return false;
        }
    }
}

/// Stops every other thread for a save: the pool's threads end (they
/// start lazily, through a helper that may still be starting them), and
/// detached drops finish. The pool stays stopped: the process exits after
/// the save.
fn quiesce() {
    std::mem::forget(crate::pool::stop());
    crate::pool::wait_detached();
}

/// `save` in a forked child (`LUST_FRONT_SAVE=background`), so the build
/// answers and exits at once and a release publishes its artifact without
/// waiting (a base save takes 10-18 s on tsgo). A release build's cc step
/// runs after the fork, in the parent (`driver::defer_cc`), so the save
/// overlaps clang; the child drops it first. The child is this
/// process's memory at the fork with this thread alone; it detaches (its
/// own session, standard streams on /dev/null, so no pipe of the caller
/// waits for it), holds the state lock until it exits (`lock`), and
/// writes its result line to `save.log` in the state directory. Here the
/// session is leaked: the process exits next. Saves here when the fork
/// fails.
pub fn save_background(dir: &Path, roots: Box<Roots>) -> Result<String, String> {
    use std::os::fd::AsRawFd;
    if !arena_on() {
        return Err("not an image process".into());
    }
    // Before the fork: the child gets only this thread.
    quiesce();
    let build_pid = std::process::id();
    let log = dir.join(SAVE_LOG);
    let _ = std::fs::remove_file(&log);
    let null = std::fs::OpenOptions::new().read(true).write(true).open("/dev/null").map_err(|e| format!("/dev/null: {e}"))?;
    // SAFETY: no other thread runs (`quiesce`), so the child's copy of
    // the heap and of every lock in it is consistent.
    let pid = unsafe { fork() };
    if pid == 0 {
        // SAFETY: calls on this process's own session and descriptors.
        unsafe {
            setsid();
            (0..3).for_each(|fd| {
                dup2(null.as_raw_fd(), fd);
            });
        }
        // The parent runs a parked cc step after the fork (`driver::defer_cc`): its unit
        // texts are freed here, so they are not live blocks of the image.
        crate::driver::drop_parked_cc();
        // A base from this heap would keep its scattered pages: rebuild the image cold instead
        // (`compaction_due`), unless a job of its own does that. On success the exec does not
        // return.
        if compaction_due(dir) && std::env::var_os(COMPACT_ENV).is_none_or(|v| v != "defer") {
            let why = compact_exec(build_pid);
            refuse_compaction(dir, &why);
        }
        let line = write_image(dir, roots).unwrap_or_else(|e| format!("lust: front state not saved: {e}"));
        let _ = std::fs::write(&log, line + "\n");
        // SAFETY: ends the child now; the parent's exit handlers and
        // buffered output are the parent's to run.
        unsafe { _exit(0) }
    }
    if pid < 0 {
        // No child: a parked cc step runs first, so its unit texts are freed before the save.
        crate::driver::finish_parked_cc();
        return write_image(dir, roots);
    }
    std::mem::forget(roots);
    Ok(format!("lust: front state saving in the background: pid {pid}, result in {}", log.display()))
}

/// Writes the image of `roots` and returns a one-line summary. After a
/// cold build, or when the deltas on the base grew large or many, a new
/// base: the restored runs whole (zero pages as holes) plus the arena's
/// live pages, and the old deltas go. Else a delta on top of the loaded
/// layers: only the restored pages this process wrote, plus the arena's
/// live pages. Files go through a temp name and a rename, so a mapped
/// layer is never written. The caller settles the session first; other
/// threads stop here (`quiesce`).
pub fn save(dir: &Path, roots: Box<Roots>) -> Result<String, String> {
    if !arena_on() {
        return Err("not an image process".into());
    }
    quiesce();
    write_image(dir, roots)
}

/// `save` once no other thread runs.
fn write_image(dir: &Path, roots: Box<Roots>) -> Result<String, String> {
    use std::io::{Seek, SeekFrom, Write};
    use std::os::fd::AsRawFd;
    let t = std::time::Instant::now();
    std::fs::create_dir_all(dir).map_err(|e| format!("state dir: {e}"))?;
    // Under the lock, a temp layer is that of a save that died (a killed
    // background child): it would ride along in a cached directory.
    if LOCKED.load(Ordering::Relaxed) {
        for e in std::fs::read_dir(dir).into_iter().flatten().flatten() {
            if e.file_name().to_string_lossy().starts_with("front.tmp") {
                let _ = std::fs::remove_file(e.path());
            }
        }
    }
    let restored = restored_runs();
    let loaded = LOADED.get().filter(|_| !restored.is_empty());
    let delta = loaded.filter(|l| !base_due(l));
    if loaded.is_none() {
        // A cold base (a cold build, or a compaction): compaction may run again.
        let _ = std::fs::remove_file(dir.join(NO_COMPACT));
        let _ = std::fs::remove_file(dir.join(COMPACT_DUE));
    } else if let Some(l) = loaded.filter(|_| delta.is_none() && compaction_due(dir)) {
        // A plain base of a scattered heap (`LUST_FRONT_COMPACT=defer`, or a foreground save).
        let span: usize = l.runs.iter().map(|&(a, e)| e - a).sum();
        let _ = std::fs::write(dir.join(COMPACT_DUE), format!("{} MB of restored span for {} MB live\n", span >> 20, l.live >> 20));
    }
    let (layer, parent) = match delta {
        Some(l) => (l.layers, l.top_id),
        None => (0, 0),
    };
    // A delta: the pages this process wrote. A base: the runs whole.
    let old_runs: Vec<(usize, usize)> = if delta.is_some() { modified_runs(restored)? } else { restored.to_vec() };
    // A base over restored runs copies their untouched pages from the
    // layer files (`write_base_run`); the written ones come from memory.
    // Both are found now: nothing may allocate between the two passes.
    let base_from: Option<(Vec<(usize, usize)>, Vec<std::fs::File>)> = match loaded {
        Some(l) if delta.is_none() => {
            let files = l.files.iter().map(std::fs::File::try_clone).collect::<Result<Vec<_>, _>>().map_err(|e| format!("image: {e}"))?;
            Some((modified_runs(restored)?, files))
        }
        _ => None,
    };
    let base_fds: Vec<c_int> = base_from.as_ref().map_or(Vec::new(), |(_, f)| f.iter().map(|f| f.as_raw_fd()).collect());
    let path = layer_path(dir, layer);
    let tmp = dir.join(format!("front.tmp{}", std::process::id()));
    // Packed (`packer`): the raw layer goes to a memfd first, then
    // `pack` writes it to the temp file.
    let packer = packer();
    let mut file = match packer {
        Some(_) => {
            use std::os::fd::FromRawFd;
            // SAFETY: a new anonymous file; the File owns its descriptor.
            let fd = unsafe { memfd_create(c"lust-front-save".as_ptr(), MFD_CLOEXEC) };
            if fd < 0 {
                return Err("memfd_create failed".into());
            }
            // SAFETY: `fd` is a fresh descriptor no one else holds.
            unsafe { std::fs::File::from_raw_fd(fd) }
        }
        None => std::fs::File::create(&tmp).map_err(|e| format!("image: {e}"))?,
    };
    let fail = |tmp: &Path, e: String| {
        let _ = std::fs::remove_file(tmp);
        Err(e)
    };
    let lo = ARENA_LO.load(Ordering::Relaxed);
    let n_pages = ARENA_SIZE / PAGE;
    let (Some(bitmap), Some(iov)) = (raw(n_pages / 8), raw(IOV_MAX * std::mem::size_of::<IoVec>())) else {
        return fail(&tmp, "no memory for the save".into());
    };
    let root = Box::into_raw(roots) as u64;
    let mut w = Walk {
        lo,
        pages: bitmap.0 as *mut u64,
        pass: 1,
        blocks: 0,
        live: 0,
        outside: 0,
        unordered: false,
        last_end: 0,
        runs: std::ptr::null(),
        n_runs: 0,
        run: 0,
        pos: 0,
        iov: iov.0 as *mut IoVec,
        n_iov: 0,
        fd: file.as_raw_fd(),
        failed: false,
    };
    // From here to the end of pass 2 nothing allocates: pass 2 must visit
    // exactly the blocks pass 1 placed.
    // SAFETY: other threads are idle (the caller's contract); the visitor
    // only reads the blocks and writes into `w` and raw mappings.
    unsafe { mi_heap_visit_blocks(std::ptr::null_mut(), true, visit, &mut w as *mut Walk as *mut c_void) };
    if w.outside > 0 || w.unordered {
        let why = format!("{} live blocks outside the arena, unordered visit: {}", w.outside, w.unordered);
        unraw(bitmap);
        unraw(iov);
        return fail(&tmp, why);
    }
    // Arena page runs from the bitmap, into raw memory.
    // SAFETY: the bitmap holds n_pages bits.
    let bits = unsafe { std::slice::from_raw_parts(bitmap.0 as *const u64, n_pages / 64) };
    let bit = |p: usize| bits[p / 64] >> (p % 64) & 1 == 1;
    let mut n_runs = 0;
    let mut p = 0;
    while p < n_pages {
        if bits[p / 64] == 0 {
            p = (p / 64 + 1) * 64;
            continue;
        }
        if bit(p) && (p == 0 || !bit(p - 1)) {
            n_runs += 1;
        }
        p += 1;
    }
    let Some(runs_mem) = raw(n_runs.max(1) * 16) else {
        unraw(bitmap);
        unraw(iov);
        return fail(&tmp, "no memory for the run list".into());
    };
    let runs = runs_mem.0 as *mut (usize, usize);
    let (mut i, mut p, mut arena_bytes) = (0, 0, 0);
    while p < n_pages {
        if bits[p / 64] == 0 {
            p = (p / 64 + 1) * 64;
            continue;
        }
        if bit(p) {
            let s = p;
            while p < n_pages && bit(p) {
                p += 1;
            }
            // SAFETY: i < n_runs, the buffer's length.
            unsafe { *runs.add(i) = (lo + s * PAGE, lo + p * PAGE) };
            arena_bytes += (p - s) * PAGE;
            i += 1;
        } else {
            p += 1;
        }
    }
    // The session's live bytes after this save (estimate): the restored
    // ones not freed, plus the arena's. The image maps every restored run,
    // dead space included. Dead blocks are zero (frees of restored blocks
    // zero them), so a base writes them as holes and the files stay near
    // the live size: a full rebuild's large delta makes the next save a
    // base (`delta` above). Only the span grows, and mapping costs nothing
    // until touched; past `MAX_SPAN` (the pagemap scan of a delta save and
    // the run count grow with it) the image goes and the next build is
    // cold.
    let old_live = loaded.map_or(0, |l| (l.live as usize).saturating_sub(OLD_FREED.load(Ordering::Relaxed)));
    let live = old_live + w.live;
    let span: usize = restored.iter().map(|&(a, e)| e - a).sum::<usize>() + arena_bytes;
    if span > MAX_SPAN {
        unraw(bitmap);
        unraw(iov);
        unraw(runs_mem);
        let _ = std::fs::remove_file(&tmp);
        let mut k = 0;
        while std::fs::remove_file(layer_path(dir, k)).is_ok() {
            k += 1;
        }
        return Ok(format!("lust: front state dropped: {} MB mapped for {} MB live; the next build is cold", span >> 20, live >> 20));
    }
    let n_regions = old_runs.len() + n_runs;
    let data_at = (HEADER + n_regions * 24).div_ceil(PAGE) * PAGE;
    let mut ok = file.seek(SeekFrom::Start(data_at as u64)).is_ok();
    let mut old_bytes = 0;
    for &(a, e) in &old_runs {
        ok = ok
            && match (&base_from, loaded) {
                (Some((modified, _)), Some(l)) => write_base_run(&file, (data_at + old_bytes) as u64, a, e, modified, &l.src, &base_fds),
                // A delta: the restored pages this process wrote, zero ones
                // (freed blocks) as holes, which map back as zero pages.
                _ => write_sparse(&mut file, a, e - a),
            };
        old_bytes += e - a;
    }
    // `write_base_run` writes at offsets: put the file where pass 2 goes on.
    ok = ok && file.seek(SeekFrom::Start((data_at + old_bytes) as u64)).is_ok();
    w.pass = 2;
    w.last_end = 0;
    w.runs = runs;
    w.n_runs = n_runs;
    if ok {
        // SAFETY: as pass 1; the heap did not change since.
        unsafe { mi_heap_visit_blocks(std::ptr::null_mut(), true, visit, &mut w as *mut Walk as *mut c_void) };
        w.advance(usize::MAX);
        w.flush();
        ok = !w.failed && !w.unordered;
    }
    // Allocation is fine again: the data is written.
    let mut regions: Vec<(u64, u64, u64)> = Vec::with_capacity(n_regions);
    let mut off = data_at as u64;
    for &(a, e) in &old_runs {
        regions.push((a as u64, (e - a) as u64, off));
        off += (e - a) as u64;
    }
    for i in 0..n_runs {
        // SAFETY: i < n_runs.
        let (a, e) = unsafe { *runs.add(i) };
        regions.push((a as u64, (e - a) as u64, off));
        off += (e - a) as u64;
    }
    unraw(bitmap);
    unraw(iov);
    unraw(runs_mem);
    let id = {
        let now = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_or(0, |d| d.as_nanos() as u64);
        (now ^ (std::process::id() as u64).rotate_left(40)) | 1
    };
    let h = Header {
        build: build_id(),
        anchors: anchors(),
        root,
        next_base: (lo + ARENA_SIZE) as u64,
        generation: GEN.load(Ordering::Relaxed) as u64,
        live: live as u64,
        id,
        parent,
        regions,
        packed: None,
    };
    // A trailing hole leaves the file short of its last region's end.
    ok = ok && file.set_len(off).is_ok();
    ok = ok && file.seek(SeekFrom::Start(0)).is_ok() && file.write_all(&h.bytes()).is_ok();
    ok = ok && file.metadata().is_ok_and(|m| m.len() == off);
    if !ok {
        return fail(&tmp, "image write failed".into());
    }
    let mut packed_len = None;
    if let Some(z) = packer {
        let mut out = match std::fs::File::create(&tmp) {
            Ok(f) => f,
            Err(e) => return fail(&tmp, format!("image: {e}")),
        };
        match pack(&file, off, &h.bytes(), &mut out, z) {
            Ok(n) => packed_len = Some(n),
            Err(e) => return fail(&tmp, e),
        }
    }
    drop(file);
    if let Err(e) = std::fs::rename(&tmp, &path) {
        return fail(&tmp, format!("image rename: {e}"));
    }
    // Deltas above the layer just written are stale now.
    let mut k = layer + 1;
    while std::fs::remove_file(layer_path(dir, k)).is_ok() {
        k += 1;
    }
    Ok(format!(
        "lust: front state saved: generation {} as {}, {} blocks, {} MB new + {} MB {}, {:.0} ms, {} MB live ({} MB of restored blocks freed){}",
        h.generation,
        if layer == 0 { "base".to_string() } else { format!("delta {layer}") },
        w.blocks,
        arena_bytes >> 20,
        old_bytes >> 20,
        if layer == 0 { "kept" } else { "rewritten" },
        t.elapsed().as_secs_f64() * 1e3,
        live >> 20,
        OLD_FREED.load(Ordering::Relaxed) >> 20,
        packed_len.map_or_else(|| format!(", {}", raw_why().unwrap_or("raw")), |n| format!(", packed to {} MB", n >> 20))
    ))
}

/// Removes the image (after a compile that panicked on a restored session).
pub fn discard(dir: &Path) {
    let _ = std::fs::remove_file(layer_path(dir, 0));
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A raw layer packs and unpacks to the same bytes, and its zero pages
    /// stay holes in the memfd. Skipped where libzstd is missing.
    #[test]
    fn pack_round_trip() {
        let Some(z) = zstd() else { return };
        let dir = std::env::temp_dir().join(format!("lust-pack-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let len = 3 * SECTION + 5 * PAGE;
        // Every third page zero, the others a pattern.
        let data: Vec<u8> = (0..len).map(|i| if (i / PAGE) % 3 == 1 { 0 } else { (i * 31 % 251) as u8 }).collect();
        std::fs::write(dir.join("raw"), &data).unwrap();
        let raw = std::fs::File::open(dir.join("raw")).unwrap();
        let head = header(9, 0).bytes();
        let mut out = std::fs::File::create(dir.join("packed")).unwrap();
        let n = pack(&raw, len as u64, &head, &mut out, z).unwrap();
        drop(out);
        let packed = std::fs::read(dir.join("packed")).unwrap();
        assert_eq!(packed.len() as u64, n);
        assert_eq!(&packed[..8], MAGIC_PACKED);
        let word = |i: usize| u64::from_le_bytes(packed[i..i + 8].try_into().unwrap());
        assert_eq!((word(8), word(24)), (len as u64, head.len() as u64));
        let at = 32 + head.len();
        let sections: Vec<(u64, u64, u64)> =
            (0..word(16) as usize).map(|k| (word(at + 24 * k), word(at + 24 * k + 8), word(at + 24 * k + 16))).collect();
        assert_eq!(sections.len(), len.div_ceil(SECTION));
        let mem = unpack(&dir.join("packed"), len as u64, &sections, z).unwrap();
        let mut back = vec![0u8; len];
        assert!(read_full_at(&mem, &mut back, 0));
        assert!(back == data, "unpacked bytes differ");
        let allocated = std::os::unix::fs::MetadataExt::blocks(&mem.metadata().unwrap()) * 512;
        assert!(allocated < len as u64 * 3 / 4, "zero pages were written: {allocated} of {len} bytes allocated");
        // A damaged byte in a section fails the check: the load goes cold.
        let mut bad = packed.clone();
        let mid = (sections[1].0 + sections[1].1 / 2) as usize;
        bad[mid] ^= 0x40;
        std::fs::write(dir.join("bad"), &bad).unwrap();
        assert!(unpack(&dir.join("bad"), len as u64, &sections, z).is_err(), "a damaged section unpacked");
        // The whole layer reads as a chain layer; a truncated one does not.
        let h = read_header(&dir.join("packed")).unwrap();
        assert_eq!((h.id, h.packed.as_ref().map(|p| p.1.len())), (9, Some(sections.len())));
        std::fs::write(dir.join("short"), &packed[..packed.len() - 100]).unwrap();
        assert!(read_header(&dir.join("short")).is_err(), "a truncated layer read");
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn overlay_keeps_the_topmost_layer() {
        let base = vec![(0x1000, 0x5000, 0, 100), (0x8000, 0x9000, 0, 200)];
        let delta = vec![(0x2000, 0x3000, 1, 10), (0x4000, 0x8800, 1, 20)];
        let want = vec![
            (0x1000, 0x2000, 0, 100),
            (0x2000, 0x3000, 1, 10),
            (0x3000, 0x4000, 0, 100 + 0x2000),
            (0x4000, 0x8800, 1, 20),
            (0x8800, 0x9000, 0, 200 + 0x800),
        ];
        assert_eq!(overlay(&base, &delta), want);
        assert_eq!(overlay(&[], &base), base);
    }

    /// A copy keeps the source's data and its holes (a sparse base stays
    /// sparse), at another offset.
    #[test]
    fn copy_extents_keeps_holes() {
        use std::os::fd::AsRawFd;
        use std::os::unix::fs::FileExt;
        let dir = std::env::temp_dir().join(format!("lust-image-copy-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let (sp, dp) = (dir.join("src"), dir.join("dst"));
        let src = std::fs::File::options().create(true).truncate(true).read(true).write(true).open(&sp).unwrap();
        src.write_all_at(&[7u8; PAGE], 0).unwrap();
        src.write_all_at(&[9u8; PAGE], 64 * PAGE as u64).unwrap();
        let dst = std::fs::File::options().create(true).truncate(true).read(true).write(true).open(&dp).unwrap();
        assert!(copy_extents(src.as_raw_fd(), 0, dst.as_raw_fd(), PAGE as u64, 65 * PAGE as u64));
        dst.set_len(66 * PAGE as u64).unwrap();
        let mut page = vec![0u8; PAGE];
        dst.read_exact_at(&mut page, PAGE as u64).unwrap();
        assert!(page.iter().all(|&b| b == 7));
        dst.read_exact_at(&mut page, 65 * PAGE as u64).unwrap();
        assert!(page.iter().all(|&b| b == 9));
        dst.read_exact_at(&mut page, 30 * PAGE as u64).unwrap();
        assert!(page.iter().all(|&b| b == 0));
        // The gap is a hole on file systems that keep them (data starts
        // again only at the second page's copy).
        // SAFETY: lseek on an open fd.
        let next = unsafe { lseek(dst.as_raw_fd(), 2 * PAGE as i64, 3) };
        assert!(next < 0 || next as usize >= 2 * PAGE, "data at {next}");
        let _ = std::fs::remove_dir_all(&dir);
    }

    fn header(id: u64, parent: u64) -> Header {
        Header {
            build: build_id(),
            anchors: anchors(),
            root: 0x1000_0000_1000,
            next_base: (WINDOW_LO + ARENA_SIZE) as u64,
            generation: 3,
            live: 42 << 20,
            id,
            parent,
            regions: vec![(0x1000_0000_0000, 2 * PAGE as u64, PAGE as u64), (0x1000_0010_0000, PAGE as u64, 3 * PAGE as u64)],
            packed: None,
        }
    }

    /// A layer file: the header, then zero pages up to the last region's end.
    fn write_layer(path: &Path, h: &Header) {
        let mut b = h.bytes();
        b.resize(4 * PAGE, 0);
        std::fs::write(path, b).unwrap();
    }

    /// The header reads back field for field, and a region that runs past
    /// the file's end, or a foreign magic, is refused.
    #[test]
    fn header_round_trips_and_rejects_bad_tables() {
        let dir = std::env::temp_dir().join(format!("lust-image-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let p = dir.join("h.img");
        let h = header(7, 0);
        write_layer(&p, &h);
        let back = read_header(&p).unwrap();
        assert_eq!((back.root, back.next_base, back.generation, back.live, back.id, back.parent), (h.root, h.next_base, 3, 42 << 20, 7, 0));
        assert_eq!(back.regions, h.regions);
        assert!(back.compatible(), "same build, same process");
        let mut short = h.bytes();
        short.resize(2 * PAGE, 0);
        std::fs::write(&p, short).unwrap();
        assert!(read_header(&p).is_err(), "a region past the end of the file");
        let mut foreign = h.bytes();
        foreign[0] = b'X';
        foreign.resize(4 * PAGE, 0);
        std::fs::write(&p, foreign).unwrap();
        assert!(read_header(&p).is_err(), "magic");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// The chain is the base, then each delta whose parent is the layer
    /// before it: a delta left from another chain ends it.
    #[test]
    fn chain_stops_at_a_stale_delta() {
        let dir = std::env::temp_dir().join(format!("lust-image-chain-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        write_layer(&layer_path(&dir, 0), &header(10, 0));
        write_layer(&layer_path(&dir, 1), &header(11, 10));
        write_layer(&layer_path(&dir, 2), &header(12, 99));
        let chain = read_chain(&dir).unwrap();
        assert_eq!(chain.iter().map(|h| h.id).collect::<Vec<_>>(), vec![10, 11]);
        write_layer(&layer_path(&dir, 0), &header(10, 5));
        assert!(read_chain(&dir).is_err(), "a base must have no parent");
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn arena_bases_parse_and_stay_in_the_window() {
        let hex = |s: &std::ffi::CStr| parse_hex(s.as_ptr());
        assert_eq!(hex(c"100000000000"), Some(WINDOW_LO));
        assert_eq!(hex(c""), None);
        assert_eq!(hex(c"12z"), None);
        assert!(valid_base(WINDOW_LO) && valid_base(WINDOW_HI - ARENA_SIZE));
        assert!(!valid_base(WINDOW_HI - ARENA_SIZE + (1 << 30)), "past the window's end");
        assert!(!valid_base(WINDOW_LO + 4096), "not 1 GiB aligned");
        assert!(!valid_base(0));
    }
}
