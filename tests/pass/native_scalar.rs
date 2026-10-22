mod native {
    pub type CInt = i32;
    unsafe extern "C" {
        pub fn abs(value: CInt) -> CInt;
        pub fn labs(value: isize) -> isize;
        pub fn llabs(value: i64) -> i64;
        pub fn srand(seed: u32);
        pub fn rand() -> i32;
        pub fn getpid() -> i32;
    }
}
use native::abs as magnitude;

fn main() {
    let captured = unsafe {
        assert_eq!(magnitude(-17), 17);
        assert_eq!(native::labs(-2147483649), 2147483649);
        assert_eq!(native::llabs(-4294967297), 4294967297);
        assert!(native::getpid() > 0);
        let unit: () = native::srand(123);
        assert_eq!(unit, ());
        let first = native::rand();
        native::srand(123);
        assert_eq!(first, native::rand());
        || magnitude(-29)
    };
    assert_eq!(captured(), 29);
    let abs = |n: i32| n + 1;
    assert_eq!(abs(3), 4);
    println!("scalar imports, aliases, void calls, effects, and closures: ok");
}
