use crate::{Map, Number, Value};

mod sealed {
    pub trait Sealed {}
}

/// Deliberately sealed: this bound is not serde::Serialize.
#[doc(hidden)]
pub trait JsonInput: sealed::Sealed {
    fn __json_value(&self) -> Value;
}

impl sealed::Sealed for Value {}
impl JsonInput for Value {
    fn __json_value(&self) -> Value { self.clone() }
}
impl sealed::Sealed for bool {}
impl JsonInput for bool {
    fn __json_value(&self) -> Value { Value::Bool(*self) }
}
impl sealed::Sealed for str {}
impl JsonInput for str {
    fn __json_value(&self) -> Value { Value::String(self.to_string()) }
}
impl sealed::Sealed for String {}
impl JsonInput for String {
    fn __json_value(&self) -> Value { Value::String(self.clone()) }
}
impl sealed::Sealed for Map<String, Value> {}
impl JsonInput for Map<String, Value> {
    fn __json_value(&self) -> Value { Value::Object(self.clone()) }
}

macro_rules! integers {
    ($($ty:ty),* $(,)?) => {$(
        impl sealed::Sealed for $ty {}
        impl JsonInput for $ty {
            fn __json_value(&self) -> Value { Value::Number(Number::from(*self)) }
        }
    )*};
}
integers!(i8, i16, i32, i64, u8, u16, u32, u64);
#[cfg(any(target_pointer_width = "16", target_pointer_width = "32", target_pointer_width = "64"))]
integers!(isize, usize);

impl<T: ?Sized + JsonInput> sealed::Sealed for &T {}
impl<T: ?Sized + JsonInput> JsonInput for &T {
    fn __json_value(&self) -> Value { <T as JsonInput>::__json_value(*self) }
}
impl<T: JsonInput> sealed::Sealed for [T] {}
impl<T: JsonInput> JsonInput for [T] {
    fn __json_value(&self) -> Value {
        let mut out = Vec::new();
        for v in self { out.push(v.__json_value()); }
        Value::Array(out)
    }
}
macro_rules! arrays {
    ($($n:literal),* $(,)?) => {$(
        impl<T: JsonInput> sealed::Sealed for [T; $n] {}
        impl<T: JsonInput> JsonInput for [T; $n] {
            fn __json_value(&self) -> Value {
                let mut out = Vec::new();
                for v in self { out.push(v.__json_value()); }
                Value::Array(out)
            }
        }
    )*};
}
arrays!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
        17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32);
impl<T: JsonInput> sealed::Sealed for Vec<T> {}
impl<T: JsonInput> JsonInput for Vec<T> {
    fn __json_value(&self) -> Value {
        let mut out = Vec::new();
        for v in self { out.push(v.__json_value()); }
        Value::Array(out)
    }
}
impl<T: JsonInput> sealed::Sealed for Option<T> {}
impl<T: JsonInput> JsonInput for Option<T> {
    fn __json_value(&self) -> Value {
        match self { Some(v) => v.__json_value(), None => Value::Null }
    }
}
