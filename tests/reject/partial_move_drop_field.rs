// expect: L9001
// Valid Rust. Lust codegen zeroes a moved-out field and drops the husk
// at scope exit, which would run the field's Drop impl on the zeroed
// value, so the partial move rejects until drop elaboration lands.
struct Guard {
    name: String,
}

impl Drop for Guard {
    fn drop(&mut self) {
        println!("drop [{}]", self.name);
    }
}

struct Pair {
    g: Guard,
    n: i32,
}

fn main() {
    let p = Pair { g: Guard { name: "g".to_string() }, n: 1 };
    let g = p.g;
    println!("got {}", g.name);
}
