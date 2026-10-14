// std::error::Error in source (W-STD-C phase 2): plain impls, a
// bound use, and the deprecated description() default text.
// dyn Error and source() chains wait on the dyn.std work (fmt
// supertraits in vtables, L0702).
use std::error::Error;
use std::fmt;

#[derive(Debug)]
struct Leaf(i32);

impl fmt::Display for Leaf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "leaf {}", self.0)
    }
}

impl Error for Leaf {}

#[derive(Debug)]
struct Wrap;

impl fmt::Display for Wrap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "wrap")
    }
}

impl Error for Wrap {
    fn description(&self) -> &str {
        "a wrapped thing"
    }
}

fn generic<E: Error>(e: &E) -> String {
    format!("{}|{:?}", e, e)
}

fn main() {
    println!("{}", generic(&Leaf(9)));
    println!("{}", generic(&Wrap));
    println!("desc: {} / {}", Leaf(1).description(), Wrap);
}
