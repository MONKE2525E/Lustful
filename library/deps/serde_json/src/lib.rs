//! Closed, integer-only Value construction and compact serialization.
//! This is not a Serde implementation. Unsupported inputs have no JsonInput impl.
mod convert;
mod macros;
mod number;
mod ser;
pub mod map;
pub mod value;

pub use convert::JsonInput;
pub use map::Map;
pub use number::Number;
pub use value::Value;

/// No accepted operation creates an error. The empty representation prevents
/// inventing parser/IO errors for APIs that this adapter does not implement.
#[derive(Debug)]
pub enum Error {}

impl std::fmt::Display for Error {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {}
    }
}

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
