// C compilation with tcc. Units compile to object files: a few in process with libtcc, many in
// parallel `tcc -c` processes (libtcc serializes compiles behind a global lock). libtcc then links
// in process: a standalone executable, or (for the daemon) a base shared library plus a small
// executable with the changed code.
use std::ffi::{CStr, CString, c_char, c_int, c_void};
use std::path::{Path, PathBuf};
use std::process::Command;

#[repr(C)]
struct TccState {
    _private: [u8; 0],
}

type ErrorFn = extern "C" fn(opaque: *mut c_void, msg: *const c_char);

type ReallocFn = extern "C" fn(ptr: *mut c_void, size: std::ffi::c_ulong) -> *mut c_void;

unsafe extern "C" {
    fn tcc_set_realloc(f: ReallocFn);
    fn mi_realloc(p: *mut c_void, size: usize) -> *mut c_void;
    fn mi_free(p: *mut c_void);
    fn tcc_new() -> *mut TccState;
    fn tcc_delete(s: *mut TccState);
    fn tcc_set_lib_path(s: *mut TccState, path: *const c_char);
    fn tcc_set_error_func(s: *mut TccState, opaque: *mut c_void, f: ErrorFn);
    fn tcc_set_options(s: *mut TccState, opts: *const c_char) -> c_int;
    fn tcc_set_output_type(s: *mut TccState, ty: c_int) -> c_int;
    fn tcc_compile_string(s: *mut TccState, src: *const c_char) -> c_int;
    fn tcc_add_file(s: *mut TccState, path: *const c_char) -> c_int;
    fn tcc_add_library_path(s: *mut TccState, path: *const c_char) -> c_int;
    fn tcc_add_library(s: *mut TccState, name: *const c_char) -> c_int;
    fn tcc_output_file(s: *mut TccState, path: *const c_char) -> c_int;
    fn tcc_relocate(s: *mut TccState) -> c_int;
    fn tcc_get_symbol(s: *mut TccState, name: *const c_char) -> *mut c_void;
}

// POSIX calls used by `run_in_memory` (linked from libc, always present).
unsafe extern "C" {
    fn fork() -> c_int;
    fn waitpid(pid: c_int, status: *mut c_int, options: c_int) -> c_int;
    fn _exit(code: c_int) -> !;
    fn fflush(stream: *mut c_void) -> c_int;
}

/// libtcc's allocator hook. Size 0 means free.
extern "C" fn tcc_realloc(p: *mut c_void, size: std::ffi::c_ulong) -> *mut c_void {
    // SAFETY: libtcc only passes pointers it got from this same function.
    unsafe {
        if size == 0 {
            mi_free(p);
            std::ptr::null_mut()
        } else {
            mi_realloc(p, size as usize)
        }
    }
}

/// Makes libtcc allocate with mimalloc. A warm daemon then reuses memory between builds instead
/// of faulting in fresh pages from the kernel each time. Call once, before any other tcc call.
pub fn use_mimalloc() {
    // SAFETY: sets a global function pointer before any libtcc state exists.
    unsafe { tcc_set_realloc(tcc_realloc) }
}

const TCC_OUTPUT_MEMORY: c_int = 1;
const TCC_OUTPUT_EXE: c_int = 2;
const TCC_OUTPUT_OBJ: c_int = 3;
const TCC_OUTPUT_DLL: c_int = 4;

extern "C" fn on_error(opaque: *mut c_void, msg: *const c_char) {
    // SAFETY: `opaque` is the `Vec<String>` owned by `Tcc`, alive for the state's lifetime.
    let errs = unsafe { &mut *(opaque as *mut Vec<String>) };
    // SAFETY: tcc passes a valid NUL-terminated message.
    errs.push(unsafe { CStr::from_ptr(msg) }.to_string_lossy().into_owned());
}

/// A libtcc state. Errors collect into `errs`.
struct Tcc {
    s: *mut TccState,
    /// Boxed so its address stays fixed: libtcc keeps a pointer to it for the error callback.
    #[allow(clippy::box_collection)]
    errs: Box<Vec<String>>,
}

impl Tcc {
    fn new(output: c_int, debug: bool) -> Result<Tcc, String> {
        let lib = CString::new(env!("LUST_TCC_LIB_PATH")).unwrap();
        // No asynchronous unwind tables: tcc writes overlapping .eh_frame
        // FDEs (spike K6), which makes the system linker reject its
        // objects. Lust frames never unwind, so the tables are pure cost.
        let opts =
            CString::new(if debug { "-g -w -fno-asynchronous-unwind-tables" } else { "-w -fno-asynchronous-unwind-tables" }).unwrap();
        // SAFETY: a fresh libtcc state; the error vector is boxed so its address is stable.
        unsafe {
            let s = tcc_new();
            if s.is_null() {
                return Err("tcc_new failed".into());
            }
            let mut t = Tcc { s, errs: Box::default() };
            tcc_set_error_func(s, &mut *t.errs as *mut Vec<String> as *mut c_void, on_error);
            tcc_set_lib_path(s, lib.as_ptr());
            tcc_set_options(s, opts.as_ptr());
            tcc_set_output_type(s, output);
            Ok(t)
        }
    }
    fn fail(&self, what: &str) -> String {
        format!("tcc failed to {what} (this is a lust bug):\n{}", self.errs.join("\n"))
    }
}

impl Drop for Tcc {
    fn drop(&mut self) {
        // SAFETY: `s` came from tcc_new and is deleted once.
        unsafe { tcc_delete(self.s) }
    }
}

fn cstr(p: &Path) -> CString {
    CString::new(p.to_string_lossy().as_bytes()).expect("path contains NUL")
}

/// Compiles `(object path, C source)` pairs.
pub fn compile_units(units: &[(PathBuf, String)], debug: bool) -> Result<(), String> {
    if units.len() <= 2 {
        for (obj, src) in units {
            let tcc = Tcc::new(TCC_OUTPUT_OBJ, debug)?;
            let c = CString::new(src.as_str()).map_err(|_| "generated C contains a NUL byte".to_string())?;
            // SAFETY: valid state and NUL-terminated strings that outlive the calls.
            unsafe {
                if tcc_compile_string(tcc.s, c.as_ptr()) != 0 {
                    return Err(tcc.fail("compile the generated C"));
                }
                if tcc_output_file(tcc.s, cstr(obj).as_ptr()) != 0 {
                    return Err(tcc.fail("write an object file"));
                }
            }
        }
        return Ok(());
    }
    let mut children = Vec::with_capacity(units.len());
    for (obj, src) in units {
        let c = obj.with_extension("c");
        std::fs::write(&c, src).map_err(|e| format!("cannot write {}: {e}", c.display()))?;
        let mut cmd = Command::new(env!("LUST_TCC_BIN"));
        cmd.arg("-c").arg("-w").arg("-fno-asynchronous-unwind-tables");
        if debug {
            cmd.arg("-g");
        }
        cmd.arg("-o").arg(obj).arg(&c);
        children.push(cmd.stderr(std::process::Stdio::piped()).spawn().map_err(|e| format!("cannot run tcc: {e}"))?);
    }
    let mut errors = String::new();
    for child in children {
        let out = child.wait_with_output().map_err(|e| format!("tcc failed: {e}"))?;
        if !out.status.success() {
            errors.push_str(&String::from_utf8_lossy(&out.stderr));
            // A child killed by a signal (for example the out-of-memory killer)
            // prints nothing; it still failed, and its object is missing or stale.
            if out.stderr.is_empty() {
                errors.push_str(&format!("tcc exited with {}\n", out.status));
            }
        }
    }
    if errors.is_empty() { Ok(()) } else { Err(format!("tcc failed to compile the generated C (this is a lust bug):\n{errors}")) }
}

fn link_objects(tcc: &Tcc, objs: &[PathBuf], out: &Path) -> Result<(), String> {
    // The float methods call libm (sqrt, pow, exp, log, floor, ...),
    // the same entry points rustc lowers them to on this platform.
    let libm = CString::new("m").unwrap();
    // SAFETY: valid state and NUL-terminated strings that outlive the calls.
    unsafe {
        if tcc_add_library(tcc.s, libm.as_ptr()) != 0 {
            return Err(tcc.fail("load libm"));
        }
        for o in objs {
            if tcc_add_file(tcc.s, cstr(o).as_ptr()) != 0 {
                return Err(tcc.fail("load an object file"));
            }
        }
        if tcc_output_file(tcc.s, cstr(out).as_ptr()) != 0 {
            return Err(tcc.fail("link"));
        }
    }
    Ok(())
}

/// Links object files into a shared library at `out`.
pub fn link_shared(objs: &[PathBuf], out: &Path, debug: bool) -> Result<(), String> {
    let tcc = Tcc::new(TCC_OUTPUT_DLL, debug)?;
    link_objects(&tcc, objs, out)
}

/// Links an executable from `objs` plus `<dir>/lib<base>.so`, which it loads at run time.
/// The base name is versioned (for example `base-3`), so a rebuilt base never changes what an
/// executable built earlier loads.
pub fn link_with_base(objs: &[PathBuf], dir: &Path, base: &str, out: &Path, debug: bool) -> Result<(), String> {
    let tcc = Tcc::new(TCC_OUTPUT_EXE, debug)?;
    let rpath = CString::new(format!("-Wl,-rpath={}", dir.display())).unwrap();
    let base = CString::new(base).unwrap();
    // SAFETY: valid state and NUL-terminated strings that outlive the calls.
    unsafe {
        tcc_set_options(tcc.s, rpath.as_ptr());
        tcc_add_library_path(tcc.s, cstr(dir).as_ptr());
        if tcc_add_library(tcc.s, base.as_ptr()) != 0 {
            return Err(tcc.fail("load libbase.so"));
        }
    }
    link_objects(&tcc, objs, out)
}

/// Links object files into a standalone executable at `out`.
pub fn link(objs: &[PathBuf], out: &Path, debug: bool) -> Result<(), String> {
    let tcc = Tcc::new(TCC_OUTPUT_EXE, debug)?;
    link_objects(&tcc, objs, out)
}

/// The runtime unit compiled to an object once per lust build, cached in the temp directory.
/// The key is a hash of the runtime source, the debug flag, and the tcc library path: anything
/// that changes the object's bytes changes the key. Stale entries are left for the OS to clean.
pub fn cached_runtime_object(runtime_src: &str, debug: bool) -> Result<PathBuf, String> {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    runtime_src.hash(&mut h);
    debug.hash(&mut h);
    env!("LUST_TCC_LIB_PATH").hash(&mut h);
    // The compile options change the object's bytes too; name the set so
    // a flag change does not reuse an object built without it.
    "opts:no-asynchronous-unwind-tables".hash(&mut h);
    let obj = std::env::temp_dir().join(format!("lust-runtime-{:016x}.o", h.finish()));
    if obj.exists() {
        return Ok(obj);
    }
    // Build under a private name, then rename, so two lust processes never see a half object.
    let tmp = std::env::temp_dir().join(format!("lust-runtime-{}-{}.o", std::process::id(), if debug { "g" } else { "o" }));
    compile_units(&[(tmp.clone(), runtime_src.to_string())], debug)?;
    match std::fs::rename(&tmp, &obj) {
        Ok(()) => {}
        // Another process won the race (or the rename failed): use the file that is there,
        // else keep our own copy.
        Err(_) if obj.exists() => {
            let _ = std::fs::remove_file(&tmp);
        }
        Err(_) => return Ok(tmp),
    }
    Ok(obj)
}

/// Compiles `units` (C sources; object paths are ignored) plus the cached runtime object into
/// memory and runs the program's `main` with `argv` (argv[0] included). Returns the exit code
/// exactly as the file-based `lust run` reports it: the program's own code, or 134 when it died
/// by a signal (a panic aborts). No object files, no link, no exec of a built binary. Use only
/// for small programs in a one-shot process: libtcc compiles serially here.
///
/// Compilation, relocation, and the symbol lookup happen in this process and can fail with
/// Err (the caller then falls back to the file-based path; user code has not run). The call
/// into user code happens in a forked child, so a panic or crash in the program cannot kill
/// this process, exit codes match the file-based path, and the child's C stdio buffering sees
/// the same fds a real executable would. The child inherits our stdout and stderr.
///
/// The fork contract: a fork copies only the calling thread, and a thread that holds a lock at
/// the fork (the allocator's, stdio's) leaves it held in the child for good. So no other thread
/// may live at the fork. This call stops the compiler's pool (`pool::stop` joins every pool
/// thread), then `lone_thread` checks the OS thread list and any other live thread gives Err
/// before the fork. The pool stays stopped only until the fork returns. The caller runs this
/// only in one-shot sessions (a daemon runs guard compiles on other threads), and never from
/// inside a `par_map` task. On non-Unix targets this always returns Err.
pub fn run_in_memory(units: &[(PathBuf, String)], runtime_obj: &Path, argv: &[String], debug: bool) -> Result<i32, String> {
    #[cfg(not(unix))]
    {
        let _ = (units, runtime_obj, argv, debug);
        return Err("in-memory run is Unix-only".into());
    }
    #[cfg(unix)]
    {
        let tcc = Tcc::new(TCC_OUTPUT_MEMORY, debug)?;
        // Build argv before the fork, so the child allocates nothing before calling main.
        let cargs: Vec<CString> = argv
            .iter()
            .map(|a| CString::new(a.as_str()).map_err(|_| "program argument contains a NUL byte".to_string()))
            .collect::<Result<_, _>>()?;
        let mut cargv: Vec<*mut c_char> = cargs.iter().map(|a| a.as_ptr() as *mut c_char).collect();
        cargv.push(std::ptr::null_mut());
        // SAFETY: valid state and NUL-terminated strings that outlive the calls.
        let main_sym = unsafe {
            for (_, src) in units {
                let c = CString::new(src.as_str()).map_err(|_| "generated C contains a NUL byte".to_string())?;
                if tcc_compile_string(tcc.s, c.as_ptr()) != 0 {
                    return Err(tcc.fail("compile the generated C"));
                }
            }
            if tcc_add_file(tcc.s, cstr(runtime_obj).as_ptr()) != 0 {
                return Err(tcc.fail("load the runtime object"));
            }
            if tcc_relocate(tcc.s) != 0 {
                return Err(tcc.fail("relocate the program"));
            }
            let name = CString::new("main").unwrap();
            let sym = tcc_get_symbol(tcc.s, name.as_ptr());
            if sym.is_null() {
                return Err(tcc.fail("find main"));
            }
            // The generated main has C's standard signature: int main(int argc, char **argv).
            std::mem::transmute::<*mut c_void, extern "C" fn(c_int, *mut *mut c_char) -> c_int>(sym)
        };
        // No other thread may live at the fork (see above).
        let pool_stopped = crate::pool::stop();
        if !lone_thread() {
            return Err("another thread is alive, and an in-memory run forks".into());
        }
        // Flush Rust and C buffers before the fork, so the child does not write them twice.
        {
            use std::io::Write as _;
            let _ = std::io::stdout().flush();
            let _ = std::io::stderr().flush();
            // SAFETY: fflush(NULL) flushes all C streams.
            unsafe { fflush(std::ptr::null_mut()) };
        }
        // SAFETY: this is the process's only thread (checked above); the child only calls main
        // and _exit.
        let pid = unsafe { fork() };
        if pid == 0 {
            // Child. Do not return, drop, or panic: call user code, flush, _exit.
            // SAFETY: main_sym was relocated before the fork; cargv outlives the call.
            unsafe {
                let code = main_sym(cargs.len() as c_int, cargv.as_mut_ptr());
                fflush(std::ptr::null_mut());
                _exit(code);
            }
        }
        // Parent. The child is its own process now, so the pool may start again while the
        // program runs.
        drop(pool_stopped);
        if pid < 0 {
            return Err("fork failed for an in-memory run".into());
        }
        let mut status: c_int = 0;
        // SAFETY: pid is our child; status is a valid out-pointer.
        if unsafe { waitpid(pid, &mut status, 0) } < 0 {
            return Err("waitpid failed for an in-memory run".into());
        }
        // WIFEXITED: the low 7 bits are zero and the code is in the next byte. Any signal death
        // maps to 134, as `protocol::finish` does for the file-based run.
        Ok(if status & 0x7f == 0 { (status >> 8) & 0xff } else { 134 })
    }
}

/// True when the OS lists no thread in this process but the caller (Linux:
/// /proc/self/task). A thread joined just before can stay listed for a
/// moment while it exits, so this waits up to 50 ms for the list to settle.
/// False when the list cannot be read. Other Unix targets have no such list
/// and return true: there the pins in `run_in_memory`'s contract must hold.
#[cfg(unix)]
fn lone_thread() -> bool {
    #[cfg(target_os = "linux")]
    {
        let start = std::time::Instant::now();
        loop {
            let Ok(list) = std::fs::read_dir("/proc/self/task") else { return false };
            if list.count() <= 1 {
                return true;
            }
            // A joined pool thread can stay in the task list while the kernel reaps it; on a
            // loaded machine that took over 50 ms (gates at load 150 fell back to the file run).
            if start.elapsed() > std::time::Duration::from_millis(500) {
                return false;
            }
            std::thread::sleep(std::time::Duration::from_millis(1));
        }
    }
    #[cfg(not(target_os = "linux"))]
    true
}

#[cfg(test)]
mod tests {
    /// `lone_thread` counts every thread the OS lists, not only pool threads:
    /// a parked thread makes it false. The other side, one thread at the
    /// fork of a one-shot `lust run`, is what scripts/runtest.sh checks:
    /// every small program must take the in-memory path, and
    /// `run_in_memory` forks only when `lone_thread` holds.
    #[cfg(target_os = "linux")]
    #[test]
    fn lone_thread_sees_other_threads() {
        let (tx, rx) = std::sync::mpsc::channel::<()>();
        let parked = std::thread::spawn(move || {
            let _ = rx.recv();
        });
        assert!(!super::lone_thread());
        drop(tx);
        parked.join().unwrap();
    }
}
