// Recursive container dispatch produces a leaf count, not JSON.
trait JsonPrereqInput { fn json_prereq_count(&self) -> usize; }
impl JsonPrereqInput for str {
    fn json_prereq_count(&self) -> usize { 1 }
}
impl<T: ?Sized + JsonPrereqInput> JsonPrereqInput for &T {
    fn json_prereq_count(&self) -> usize {
        <T as JsonPrereqInput>::json_prereq_count(*self)
    }
}
impl<T: JsonPrereqInput> JsonPrereqInput for [T] {
    fn json_prereq_count(&self) -> usize {
        let mut count = 0;
        for item in self.iter() { count += item.json_prereq_count(); }
        count
    }
}
impl<T: JsonPrereqInput, const N: usize> JsonPrereqInput for [T; N] {
    fn json_prereq_count(&self) -> usize {
        <[T] as JsonPrereqInput>::json_prereq_count(&self[..])
    }
}
impl<T: JsonPrereqInput> JsonPrereqInput for Vec<T> {
    fn json_prereq_count(&self) -> usize {
        <[T] as JsonPrereqInput>::json_prereq_count(&self[..])
    }
}
impl<T: JsonPrereqInput> JsonPrereqInput for Option<T> {
    fn json_prereq_count(&self) -> usize {
        match self { Some(item) => item.json_prereq_count(), None => 0 }
    }
}
fn json_prereq_count<T: ?Sized + JsonPrereqInput>(value: &T) -> usize {
    value.json_prereq_count()
}
fn main() {
    let defaults = ["ControlLeft", "MetaLeft"];
    let empty: [&str; 0] = [];
    let slice: &[&str] = &defaults[..];
    for _ in 0..8 {
        assert_eq!(json_prereq_count(&empty), 0);
        assert_eq!(json_prereq_count(&["x"]), 1);
        assert_eq!(json_prereq_count(&defaults), 2);
        assert_eq!(json_prereq_count(&["x"; 33]), 33);
        assert_eq!(json_prereq_count::<[&str]>(slice), 2);
        assert_eq!(json_prereq_count(&&&slice), 2);
        assert_eq!(json_prereq_count(&[defaults, defaults]), 4);
        let nested = vec![Some(vec![defaults]), None, Some(vec![defaults])];
        assert_eq!(json_prereq_count(&nested), 4);
        let none: Option<Vec<[&str; 2]>> = None;
        assert_eq!(json_prereq_count(&none), 0);
    }
    assert_eq!(defaults[0], "ControlLeft");
    println!("json_prereq_const_containers ok");
}
