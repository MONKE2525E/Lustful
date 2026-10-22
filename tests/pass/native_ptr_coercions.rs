mod native {
    pub type CChar = i8;
    pub type In = *const CChar;
    pub type Out = *mut CChar;
    pub type Size = usize;
    unsafe extern "C" {
        pub fn strlen(text: In) -> Size;
        pub fn strcpy(dst: Out, src: In) -> Out;
    }
}
use native::{strlen as length, strcpy as copy};
fn main() {
    let zero = 0i8;
    let mut byte = 42i8;
    // Both reference-to-pointer coercions occur at native argument sites.
    assert_eq!(unsafe { length(&zero) }, 0);
    let returned = unsafe { copy(&mut byte, &zero) };
    assert_eq!(byte, 0);
    assert_eq!(unsafe { length(returned) }, 0);
    let expected: *mut i8 = &mut byte;
    assert_eq!(returned, expected);
    println!("native pointer aliases and coercions: ok");
}
