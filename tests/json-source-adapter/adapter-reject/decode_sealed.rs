struct Foreign;
impl serde_json::OwnedJsonDecode for Foreign {
    fn __from_json_slice(_: &[u8]) -> serde_json::Result<Self> { Ok(Foreign) }
}
fn main() {}
