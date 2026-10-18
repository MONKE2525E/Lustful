// capability: rejected: known attributes lust does not handle yet, such as `target_feature`, `crate_name` and `no_implicit_prelude` (named in the message)
// expect: L0522

#[no_implicit_prelude]
mod m {}

fn main() {}
