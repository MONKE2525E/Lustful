// core::ops::{Bound, RangeBounds}: start_bound/end_bound on the
// range kinds and on pairs, generic code over the trait, a written
// impl, and the std paths naming the Drain types.

use std::ops::Bound::*;
use std::ops::RangeBounds;

fn show<R: RangeBounds<usize>>(r: R, len: usize) {
    let s = match r.start_bound() {
        Included(&n) => n,
        Excluded(&n) => n.checked_add(1).expect("start"),
        Unbounded => 0,
    };
    let e = match r.end_bound() {
        Included(&n) => n.checked_add(1).expect("end"),
        Excluded(&n) => n,
        Unbounded => len,
    };
    println!("{s}..{e}");
}

fn gd<R: RangeBounds<usize>>(v: &mut Vec<i32>, r: R) -> Vec<i32> {
    v.drain(r).collect()
}

struct Window {
    lo: usize,
    hi: usize,
}

impl RangeBounds<usize> for Window {
    fn start_bound(&self) -> std::ops::Bound<&usize> {
        Included(&self.lo)
    }
    fn end_bound(&self) -> std::ops::Bound<&usize> {
        Excluded(&self.hi)
    }
}

fn first_two(mut d: std::vec::Drain<'_, i32>) -> i32 {
    d.next().unwrap_or(0) + d.next().unwrap_or(0)
}

fn chars_of(d: std::string::Drain<'_>) -> usize {
    d.count()
}

fn exact<I: ExactSizeIterator>(i: &I) -> usize {
    i.len()
}

fn main() {
    show(2..5, 9);
    show(..3, 9);
    show(2.., 9);
    show(.., 9);
    show(1..=4, 9);
    show(..=4, 9);
    show((Excluded(1), Included(3)), 9);
    show((Unbounded::<usize>, Unbounded::<usize>), 9);
    // Concrete bound calls as well.
    let full = ..;
    let full_start: std::ops::Bound<&usize> = full.start_bound();
    println!("{:?} {:?} {:?}", (2usize..5).start_bound(), (2usize..5).end_bound(), full_start);
    println!("{:?} {:?}", (1usize..).end_bound(), (..=7usize).end_bound());
    println!("{:?} {:?}", (Included(1usize), Excluded(9usize)).start_bound(), (Included(1usize), Excluded(9usize)).end_bound());
    let mut v = vec![1, 2, 3, 4, 5];
    println!("{:?} {:?}", gd(&mut v, 1..3), v);
    println!("{:?} {:?}", gd(&mut v, ..=1), v);
    println!("{:?} {:?}", gd(&mut v, Window { lo: 0, hi: 1 }), v);
    let mut v = vec![10, 20, 30, 40];
    println!("ft {}", first_two(v.drain(1..4)));
    println!("v {v:?}");
    let mut s = String::from("abcd");
    println!("chars {}", chars_of(s.drain(1..3)));
    println!("s {s:?}");
    let mut v = vec![1, 2, 3];
    let d = v.drain(1..);
    println!("exact {} {} {:?}", exact(&d), d.len(), d.collect::<Vec<i32>>());
    println!("v {v:?}");
    // Bound as a plain generic enum: Debug, equality, matches.
    let b = Included(String::from("x"));
    println!("{:?} {:?} {} {}", b, Unbounded::<i32>, Included(1) == Included(1), Included(1) != Excluded(1));
}
