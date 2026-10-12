// Unwind case (PANIC=unwind): a panic is caught and the program
// continues. Abort mode cannot run this program to the same output,
// so lust must reject it until wave C adds unwinding.
fn boom() -> i32 {
    panic!("value-boom");
}

fn main() {
    // Keep the caught panic off stderr; the oracle compares stdout.
    std::panic::set_hook(Box::new(|_| {}));
    let caught = std::panic::catch_unwind(boom);
    let payload = match &caught {
        Ok(_) => "no-panic",
        Err(e) => match e.downcast_ref::<&str>() {
            Some(s) => s,
            None => "other-payload",
        },
    };
    println!("caught={} payload={}", caught.is_err(), payload);
    let ok = std::panic::catch_unwind(|| 40 + 2);
    println!("ok={:?}", ok);
}
