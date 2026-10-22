// Dedicated serde_json policy, supplied by parent-owned compiler/runtime work.
// Value's parser only constructs finite floats. This private helper does not
// authorize float JsonInput conversions or expose general Serde serialization.
pub(crate) fn write_finite_f64(value: f64, out: &mut String) {
    core::intrinsics::json_fmt_f64(out, value)
}
