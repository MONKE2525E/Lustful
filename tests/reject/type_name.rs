// expect: L0505
// std::any::type_name prints full paths; lust rejects it cleanly
// instead of printing a flat name.
mod m0 {
    pub struct Stats {
        pub n: i64,
    }
}

fn main() {
    println!("{}", std::any::type_name::<m0::Stats>());
    println!("{}", std::any::type_name::<Vec<m0::Stats>>());
}
