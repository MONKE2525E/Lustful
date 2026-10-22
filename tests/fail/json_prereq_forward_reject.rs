// expect: L0612
// Candidate diagnostic only: unsupported leaf must stay rejected through refs.
// Syntactically valid Rust, intentionally fails trait checking (E0277).
trait JsonPrereqInput { fn json_prereq_count(&self) -> usize; }
impl JsonPrereqInput for str {
    fn json_prereq_count(&self) -> usize { self.len() }
}
impl<T: ?Sized + JsonPrereqInput> JsonPrereqInput for &T {
    fn json_prereq_count(&self) -> usize {
        <T as JsonPrereqInput>::json_prereq_count(*self)
    }
}
struct JsonPrereqUnsupported;
fn json_prereq_require<T: JsonPrereqInput>(value: T) -> usize {
    value.json_prereq_count()
}
fn main() {
    let value = JsonPrereqUnsupported;
    println!("{}", json_prereq_require(&&&value));
}
