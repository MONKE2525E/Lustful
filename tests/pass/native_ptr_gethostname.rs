unsafe extern "C" { fn gethostname(name: *mut i8, len: usize) -> i32; }
fn main() {
    let mut buf = [127u8; 256];
    let rc = unsafe { gethostname(buf.as_mut_ptr().cast::<i8>(), buf.len()) };
    assert_eq!(rc, 0);
    // Observe a native write before applying Verenu's final-byte guard.
    assert!(buf.iter().any(|&byte| byte == 0));
    buf[255] = 0;
    assert!(buf.iter().any(|&byte| byte == 0));
    // Never format the buffer, even in assertion failures.
    println!("gethostname buffer: ok");
}
