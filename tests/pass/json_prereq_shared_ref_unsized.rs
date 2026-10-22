// Count text bytes: a conversion-shaped trait, not a serializer.
trait JsonPrereqInput { fn json_prereq_measure(&self) -> usize; }
impl JsonPrereqInput for str {
    fn json_prereq_measure(&self) -> usize { self.len() }
}
impl JsonPrereqInput for String {
    fn json_prereq_measure(&self) -> usize { self.len() }
}
impl<T: ?Sized + JsonPrereqInput> JsonPrereqInput for &T {
    fn json_prereq_measure(&self) -> usize {
        <T as JsonPrereqInput>::json_prereq_measure(*self)
    }
}
fn json_prereq_borrow<T: ?Sized + JsonPrereqInput>(value: &T) -> usize {
    value.json_prereq_measure()
}
fn json_prereq_owned<T: JsonPrereqInput>(value: T) -> usize {
    value.json_prereq_measure()
}
fn main() {
    let text: &str = "é";
    let owned = String::from("abc");
    assert_eq!(json_prereq_borrow::<str>(text), 2);
    assert_eq!(json_prereq_borrow::<&str>(&text), 2);
    assert_eq!(json_prereq_owned(&&&text), 2);
    assert_eq!(json_prereq_owned(&&&owned), 3);
    assert_eq!(owned, "abc");
    println!("json_prereq_shared_ref_unsized ok");
}
