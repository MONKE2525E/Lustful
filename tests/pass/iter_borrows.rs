// Borrows through iterators: items borrow the collection, not the
// iterator, so they outlive it; `iter_mut` items are disjoint.
fn main() {
    let v = vec![String::from("a"), String::from("b"), String::from("c")];
    let first = {
        let mut it = v.iter();
        it.next()
    };
    let mut it = v.iter();
    let x = it.next();
    let y = it.next();
    drop(it);
    println!("{:?} {:?} {:?}", first, x, y);
    let long = v.iter().find(|s| s.len() > 0);
    println!("{:?}", long);
    let mut w = vec![1, 2, 3];
    let mut im = w.iter_mut();
    let a = im.next().unwrap();
    let b = im.next().unwrap();
    *a += 10;
    *b += 20;
    println!("{:?}", w);
    let n = w.len();
    for x in w.iter_mut().skip(1) {
        *x += n as i32;
    }
    println!("{:?}", w);
}
