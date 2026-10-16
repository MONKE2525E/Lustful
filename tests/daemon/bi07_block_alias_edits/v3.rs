fn sizes() -> (usize, u64) {
    type C = u64;
    #[derive(Debug, Default)]
    struct H { c: C, v: Vec<C> }
    let h = H { c: 70000, v: vec![1] };
    let r = (std::mem::size_of::<H>(), h.c as u64 + h.v.len() as u64);
    {
        type u64 = u8;
        let small: u64 = 7;
        println!("{} {}", small, std::mem::size_of::<u64>());
    }
    r
}
fn main() { println!("{:?}", sizes()); }
