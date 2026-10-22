mod native {
    pub type CChar = i8;
    pub type Text = *const CChar;
    unsafe extern "C" { pub fn strlen(text: Text) -> usize; }
}
use native::strlen as length;
fn wrapped<T>(_: T, text: native::Text) -> usize {
    let captured = unsafe { || length(text) };
    captured()
}
fn main() {
    let bytes = b"native\0";
    assert_eq!(wrapped(1u32, bytes.as_ptr().cast::<i8>()), 6);
    let length = |_: i32| 99usize;
    assert_eq!(length(0), 99);
    println!("{}", unsafe { native::strlen(bytes.as_ptr().cast::<i8>()) });
}
