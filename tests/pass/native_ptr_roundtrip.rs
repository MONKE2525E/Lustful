unsafe extern "C" {
    fn strcpy(dst: *mut i8, src: *const i8) -> *mut i8;
    fn strchr(text: *const i8, ch: i32) -> *mut i8;
    fn strlen(text: *const i8) -> usize;
}
fn main() {
    let mut buf = [85u8; 10];
    let dst: *mut i8 = (&mut buf[1] as *mut u8).cast();
    let src = b"native\0";
    let returned = unsafe { strcpy(dst, src.as_ptr().cast::<i8>()) };
    assert_eq!(returned, dst);
    assert_eq!(buf, [85, 110, 97, 116, 105, 118, 101, 0, 85, 85]);
    // Mutable-to-const coercion, passing a returned pointer back to libc.
    assert_eq!(unsafe { strlen(returned) }, 6);
    assert_eq!(unsafe { strchr(returned, 110) }, returned);
    let end = unsafe { strchr(returned, 0) };
    assert_eq!(end, (&mut buf[7] as *mut u8).cast::<i8>());
    assert!(unsafe { strchr(returned, 122) }.is_null());
    println!("pointer return and guarded buffer: ok");
}
