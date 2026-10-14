// expect: L0640
use std::sync::{Mutex, PoisonError, MutexGuard};
fn main() { let m = Mutex::new(1); let r: Result<MutexGuard<i32>, PoisonError<MutexGuard<i32>>> = m.lock(); println!("{}", r.is_ok()); match m.try_lock() { _ => {} } }
