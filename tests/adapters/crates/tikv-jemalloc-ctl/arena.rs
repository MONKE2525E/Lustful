// tikv-jemalloc-ctl 0.7.0: the by-name arena form ts-rust writes
// (program.rs thread arena, jemalloc_layout.rs opt.narenas), and
// the error texts of the failure forms. The arena count itself
// is not printed: it is 1 in the adapter and a build-and-machine
// number upstream (README).
use tikv_jemalloc_ctl::{Access, AsName};

#[global_allocator]
static GLOBAL: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

fn main() {
    // The jemalloc_layout.rs forms, verbatim.
    let arenas = Access::<u32>::read(b"opt.narenas\0".name()).unwrap();
    let own = Access::<u32>::read(b"thread.arena\0".name()).unwrap();
    println!("{} {}", arenas >= 1, own);
    println!("{}", b"thread.arena\0".name().write(own).is_ok());
    let read_back: u32 = b"thread.arena\0".name().read().unwrap();
    println!("{}", read_back == own);
    // The program.rs forms: read as Option, write ignored.
    let arena: Option<u32> = b"thread.arena\0".name().read().ok();
    let _ = b"thread.arena\0".name().write(arena.unwrap());
    println!("{:?}", arena);
    // update returns the previous value.
    println!("{:?}", Access::<u32>::update(b"thread.arena\0".name(), own));
    // Failures, with upstream's texts.
    println!("{}", b"thread.arena\0".name().write(9999u32).unwrap_err());
    println!("{}", b"opt.narenas\0".name().write(2u32).unwrap_err());
    println!("{}", Access::<u32>::read(b"no.such.key\0".name()).unwrap_err());
    println!("{}", Access::<u64>::read(b"thread.arena\0".name()).unwrap_err());
    println!("{}", b"opt.narenas\0".name().as_bytes().len());
    println!("{}", b"thread.arena\0".name().value_type_str());
    println!("{}", b"version\0".name().value_type_str());
}
