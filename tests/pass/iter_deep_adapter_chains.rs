// Deep chains of builtin adapters whose `next`, `nth`, `count`, and
// `advance_by` call more than one op of the inner iterator. Lowering
// expands each op inline, so an arm that expanded an inner op twice made
// the code exponential in the chain depth: `skip(0)` x10 then `count()`
// took over 60 s to build (fx-traitdepth, fx-cgen-ice). Each arm now
// expands each inner op once; this case builds in well under a second.
fn main() {
    let v: Vec<u32> = (1..=20).collect();
    let skips = v.iter().skip(0).skip(1).skip(0).skip(2).skip(0).skip(1).skip(0).skip(0).skip(1).skip(0).skip(0).skip(1);
    println!("{}", skips.clone().count());
    let mut s = skips.clone();
    println!("{:?} {:?} {:?}", s.nth(1), s.next(), s.nth(2));
    println!("{:?}", skips.clone().last());
    println!("{}", skips.map(|x| *x).sum::<u32>());

    let peeks = v.iter().peekable().peekable().peekable().peekable().peekable().peekable().peekable().peekable();
    let peeks = peeks.peekable().peekable().peekable().peekable().peekable().peekable().peekable().peekable();
    let mut p = peeks.peekable().peekable().peekable().peekable();
    println!("{:?}", p.peek());
    println!("{:?} {:?}", p.nth(2), p.peek());
    println!("{}", p.count());

    let steps = v.iter().step_by(1).step_by(2).step_by(1).step_by(1).step_by(2).step_by(1).step_by(1).step_by(1);
    let mut st = steps.clone();
    println!("{:?} {:?} {:?}", st.next(), st.nth(0), st.nth(5));
    println!("{}", steps.clone().count());
    println!("{:?}", steps.collect::<Vec<_>>());

    let takes = v.iter().take(19).take(18).take(17).take(16).take(15).take(14).take(13).take(12).take(11).take(10);
    let mut t = takes.clone();
    println!("{:?} {:?} {:?}", t.nth(3), t.nth(20), t.next());
    println!("{}", takes.count());

    // Mixed, with the overflow forms over a range (O(1) inner `nth`).
    let mut m = (0..50u32).skip(usize::MAX - 1).peekable().take(4).skip(0).step_by(1).skip(1).peekable().skip(0);
    println!("{:?} {}", m.nth(3), m.count());
    let mut r = (0..1000u64).skip(3).step_by(2).skip(1).peekable().take(400).skip(2).step_by(3).skip(0).peekable();
    println!("{:?} {:?} {:?}", r.nth(usize::MAX), r.next(), r.nth(10));
    let mixed = (0..100u32).inspect(|x| if *x < 3 { println!("pull {x}") }).skip(1).peekable().step_by(2).skip(0).take(30).skip(2);
    println!("{}", mixed.count());
}
