// expect: L0612
// Candidate diagnostic only: const-array impl must enforce its element bound.
// Syntactically valid Rust, intentionally fails trait checking (E0277).
trait JsonPrereqInput { fn json_prereq_count(&self) -> usize; }
impl JsonPrereqInput for str {
    fn json_prereq_count(&self) -> usize { 1 }
}
impl<T: ?Sized + JsonPrereqInput> JsonPrereqInput for &T {
    fn json_prereq_count(&self) -> usize {
        <T as JsonPrereqInput>::json_prereq_count(*self)
    }
}
impl<T: JsonPrereqInput, const N: usize> JsonPrereqInput for [T; N] {
    fn json_prereq_count(&self) -> usize {
        let mut count = 0;
        for item in self.iter() { count += item.json_prereq_count(); }
        count
    }
}
struct JsonPrereqUnsupported;
fn json_prereq_require<T: JsonPrereqInput>(value: T) -> usize {
    value.json_prereq_count()
}
fn main() {
    println!("{}", json_prereq_require([JsonPrereqUnsupported]));
}
