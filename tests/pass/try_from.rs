// The ? operator error conversion: user From impl, generic errors,
// numeric widening From, closures.
#[derive(Debug)]
struct MyErr { code: i32 }
struct Wrap { msg: String }
impl From<MyErr> for Wrap {
    fn from(e: MyErr) -> Wrap { Wrap { msg: format!("wrapped {}", e.code) } }
}
fn inner(x: i32) -> Result<i32, MyErr> { if x < 0 { Err(MyErr { code: -x }) } else { Ok(x) } }
fn outer(x: i32) -> Result<i32, Wrap> {
    let v = inner(x)?;
    Ok(v + 1)
}
fn num(x: i32) -> Result<i32, i32> { if x < 0 { Err(x) } else { Ok(x) } }
fn widen(x: i32) -> Result<i32, i64> {
    let v = num(x)?;
    Ok(v)
}
fn main() {
    match outer(-3) { Ok(v) => println!("ok {}", v), Err(w) => println!("err {}", w.msg) }
    match widen(-2) { Ok(v) => println!("ok {}", v), Err(e) => println!("err {}", e) }
}

