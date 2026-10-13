// feature: closures.fn_ptr_lifetime
// form: fn pointer type with a named lifetime, fn(&'a str) -> &'a str in a struct field
struct Hooks<'a> { first: fn(&'a str) -> &'a str }
fn head(s: &str) -> &str { &s[..1] }
fn main() {
    let h = Hooks { first: head };
    let f: fn(&str) -> &str = head;
    println!("{} {}", (h.first)("abc"), f("xyz"));
}
