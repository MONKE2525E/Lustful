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
        let opts = CString::new(if debug { "-g -w" } else { "-w" }).unwrap();
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
        cmd.arg("-c").arg("-w");
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
        }
    }
    if errors.is_empty() { Ok(()) } else { Err(format!("tcc failed to compile the generated C (this is a lust bug):\n{errors}")) }
}

fn link_objects(tcc: &Tcc, objs: &[PathBuf], out: &Path) -> Result<(), String> {
    // SAFETY: valid state and NUL-terminated strings that outlive the calls.
    unsafe {
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

/// Links an executable from `objs` plus `<dir>/libbase.so`, which it loads at run time.
pub fn link_with_base(objs: &[PathBuf], dir: &Path, out: &Path, debug: bool) -> Result<(), String> {
    let tcc = Tcc::new(TCC_OUTPUT_EXE, debug)?;
    let rpath = CString::new(format!("-Wl,-rpath={}", dir.display())).unwrap();
    let base = CString::new("base").unwrap();
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
