use std::thread;
fn main() {
    let h = thread::spawn(|| { let t = thread::current(); println!("{:?} {:?}", t.id(), t.name()); 5u8 });
    let h2 = thread::spawn(|| 1); println!("{}", h2.thread().id() == h2.thread().id());
    println!("{:?}", h.thread().id());
    let r = h.join();
    println!("{:?} {:?} {:?}", r, thread::current().id(), thread::current().name());
    println!("{:?}", thread::current());
    println!("{}", h2.join().unwrap());

}
