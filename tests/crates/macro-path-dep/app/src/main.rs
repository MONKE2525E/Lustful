use util as renamed;
use renamed::m as imported;
use crate::local::util;

mod local {
    pub fn util() -> i32 { 7 }
}

// Dependency macro paths rustc 1.99 accepts: `util::m!` and `::util::m!`
// from the root, a module, a closure, and another macro.
macro_rules! h {
    () => {
        ::util::m!()
    };
}

mod b {
    pub fn f() -> i32 {
        util::m!() + ::util::m!()
    }
}

fn main() {
    // The dependency calls both a macro and a function through $crate.
    // Caller names must not capture either, through either alias form.
    macro_rules! helper { () => { 900 }; }
    fn f() -> i32 { 900 }
    assert_eq!(helper!() + f(), 1800);
    assert_eq!(imported!(), 42);
    assert_eq!(renamed::m!(), 42);
    assert_eq!(renamed(), 7);
    let k = || util::m!();
    println!("{} {} {} {}", util::m!(), b::f(), k(), h!());
}
