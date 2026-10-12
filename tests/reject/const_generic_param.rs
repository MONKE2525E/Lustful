// expect: L0614
struct Arr<const N: usize> {
    data: [i64; N],
}

fn main() {
    let a = Arr { data: [1, 2] };
    println!("{}", a.data[0]);
}
