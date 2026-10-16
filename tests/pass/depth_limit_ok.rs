// One level below rustc's recursion limit: all compile (rustc 1.99).
#![allow(dead_code)]
trait Tr {
    fn d(&self) -> u32;
}
impl Tr for u8 {
    fn d(&self) -> u32 {
        0
    }
}
impl<T: Tr> Tr for Option<T> {
    fn d(&self) -> u32 {
        1 + 0
    }
}
fn main() {
    let x: Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<Option<u8>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>> = Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(Some(1u8)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    let y = x.clone();
    println!("{} {}", x.d(), y == x);
    let v = vec![1u8, 2, 3];
    let it = v.iter().map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x).map(|x| x);
    println!("{}", it.count());
    let r: &&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&u8 = &&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&5u8;
    println!("{}", r.clone());
}
