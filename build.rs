// Links the pinned libtcc built by scripts/build-tcc.sh, and bakes in its runtime path.
use std::path::PathBuf;

fn main() {
    let root = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let tcc = std::env::var("LUST_TCC_HOME").map(PathBuf::from).unwrap_or_else(|_| root.join("third_party/tcc"));
    let lib = tcc.join("lib");
    if !lib.join("libtcc.a").exists() {
        panic!("libtcc.a not found in {}. Run scripts/build-tcc.sh first.", lib.display());
    }
    println!("cargo:rustc-link-search=native={}", lib.display());
    println!("cargo:rustc-link-lib=static=tcc");
    if std::env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("linux") {
        println!("cargo:rustc-link-lib=dylib=dl");
        println!("cargo:rustc-link-lib=dylib=pthread");
        println!("cargo:rustc-link-lib=dylib=m");
    }
    println!("cargo:rustc-env=LUST_TCC_LIB_PATH={}", lib.join("tcc").display());
    println!("cargo:rustc-env=LUST_TCC_BIN={}", tcc.join("bin/tcc").display());
    println!("cargo:rerun-if-env-changed=LUST_TCC_HOME");
    println!("cargo:rerun-if-changed=build.rs");
}
