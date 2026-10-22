use serde_json::{json, Number, Value};
fn emit(v: Value) {
    let n = match &v { Value::Number(n) => n, _ => panic!("not number") };
    println!("{} {:?} {:?} {} {} {:?} {:#?}",
        serde_json::to_string(&v).unwrap(), v.as_i64(), v.as_u64(),
        n.is_i64(), n.is_u64(), n, n);
}
macro_rules! edges {
    ($($t:ty),* $(,)?) => {$(
        emit(json!(<$t>::MIN));
        emit(json!(<$t>::MAX));
        emit(json!(0 as $t));
        emit(json!(1 as $t));
    )*};
}
fn main() {
    edges!(i8, i16, i32, i64, isize, u8, u16, u32, u64, usize);
    for n in [-1i64, 0, 1, 9007199254740991, 9007199254740992, 9007199254740993] { emit(json!(n)); }
    for n in [i64::MAX as u64, (i64::MAX as u64) + 1, u64::MAX] { emit(json!(n)); }
    assert_eq!(json!(1i64), json!(1u64));
    assert_eq!(Number::from(0i8), Number::from(0u64));
    assert_eq!(Number::from(i64::MIN).as_i64(), Some(i64::MIN));
    assert_eq!(Number::from(u64::MAX).as_i64(), None);
}
