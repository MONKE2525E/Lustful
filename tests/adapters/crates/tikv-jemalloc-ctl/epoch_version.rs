// tikv-jemalloc-ctl 0.7.0: version (exact string of the pinned
// jemalloc build) and epoch (only its step behavior is printed,
// never an absolute count another run could shift).
use tikv_jemalloc_ctl::{Access, AsName, epoch, version};

#[global_allocator]
static GLOBAL: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

fn version_bytes() -> &'static [u8] {
    b"version\0".name().read().unwrap()
}

fn version_str() -> &'static str {
    b"version\0".name().read().unwrap()
}

fn main() {
    println!("{:?}", version::read().unwrap());
    println!("{:?}", version_str());
    let bytes = version_bytes();
    println!("{} {}", bytes.len(), bytes[bytes.len() - 1]);
    let a = epoch::read().unwrap();
    let b = epoch::advance().unwrap();
    let c = epoch::advance().unwrap();
    let d = epoch::read().unwrap();
    println!("{} {} {}", b - a, c - b, d == c);
    let e = epoch::update(0).unwrap();
    println!("{} {}", e - d, epoch::read().unwrap() == e);
    epoch::write(99).unwrap();
    println!("{}", epoch::read().unwrap() - e);
    // thread.tcache.enabled: on at first, then this thread's writes stick.
    let t0: bool = b"thread.tcache.enabled\0".name().read().unwrap();
    b"thread.tcache.enabled\0".name().write(!t0).unwrap();
    let t1: bool = b"thread.tcache.enabled\0".name().read().unwrap();
    let old: bool = b"thread.tcache.enabled\0".name().update(t0).unwrap();
    let t2: bool = b"thread.tcache.enabled\0".name().read().unwrap();
    println!("{t0} {t1} {old} {t2}");
}
