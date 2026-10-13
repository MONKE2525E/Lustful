// feature: derives.unknown
// form: a proc-macro derive from another crate, as in ts-rust codegen tools with serde
// oracle: lust-only
#[derive(Debug, Deserialize)]
struct Cfg { name: String }
fn main() { println!("x"); }
