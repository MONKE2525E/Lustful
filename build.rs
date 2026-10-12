// Links the pinned libtcc built by scripts/build-tcc.sh, and bakes in its runtime path.
// Also bakes in a build hash (compiler sources plus the tcc binary and runtime files at build
// time). The disk cache uses it as part of the compiler id, so a rebuilt compiler never reads
// entries made by an older one.
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};

/// Hashes every file under `dir` (names and bytes, sorted) into `h`.
fn hash_tree(h: &mut std::collections::hash_map::DefaultHasher, dir: &Path) {
    let mut files: Vec<PathBuf> = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        if let Ok(rd) = std::fs::read_dir(&d) {
            for e in rd.flatten() {
                let p = e.path();
                if p.is_dir() {
                    stack.push(p);
                } else {
                    files.push(p);
                }
            }
        }
    }
    files.sort();
    for f in files {
        f.strip_prefix(dir).unwrap_or(&f).to_string_lossy().hash(h);
        if let Ok(bytes) = std::fs::read(&f) {
            bytes.hash(h);
        }
    }
}

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
    // Build hash: compiler sources, the shipped library sources (built into
    // the binary by src/stdload.rs, S5), the manifest, and the tcc tree.
    let mut h = std::collections::hash_map::DefaultHasher::new();
    hash_tree(&mut h, &root.join("src"));
    hash_tree(&mut h, &root.join("library"));
    if let Ok(bytes) = std::fs::read(root.join("Cargo.toml")) {
        bytes.hash(&mut h);
    }
    hash_tree(&mut h, &tcc.join("bin"));
    hash_tree(&mut h, &lib);
    println!("cargo:rustc-env=LUST_BUILD_HASH={:016x}", h.finish());
    println!("cargo:rerun-if-changed=src");
    println!("cargo:rerun-if-changed=library");
    println!("cargo:rerun-if-changed=Cargo.toml");
    println!("cargo:rerun-if-changed={}", tcc.join("bin").display());
    println!("cargo:rerun-if-changed={}", lib.display());
}
