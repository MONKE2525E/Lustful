//! Closed Value construction, owned decoding, and compact serialization.
//! This is not a Serde implementation. Unsupported inputs have no JsonInput impl.
mod convert;
mod de;
pub mod error;
// Required integration prerequisite: exact default zmij-equivalent finite output.
mod float_format;
mod macros;
mod number;
mod ser;
pub mod map;
pub mod value;

pub use convert::JsonInput;
pub use de::{from_slice, from_str, OwnedJsonDecode};
pub use error::Error;
pub use map::Map;
pub use number::Number;
pub use value::Value;

pub type Result<T> = std::result::Result<T, Error>;

pub fn to_value<T: JsonInput>(value: T) -> Result<Value> {
    Ok(value.__json_value())
}

pub fn to_string<T: ?Sized + JsonInput>(value: &T) -> Result<String> {
    let value = value.__json_value();
    let mut out = String::new();
    ser::write_value(&value, &mut out);
    Ok(out)
}
