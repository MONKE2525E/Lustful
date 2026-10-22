use std::fmt;

#[derive(Clone, PartialEq, Eq)]
enum Integral {
    Positive(u64),
    Negative(i64),
}

#[derive(Clone, PartialEq, Eq)]
pub struct Number {
    n: Integral,
}

impl Number {
    pub fn is_i64(&self) -> bool { self.as_i64().is_some() }
    pub fn is_u64(&self) -> bool { self.as_u64().is_some() }

    pub fn as_i64(&self) -> Option<i64> {
        match &self.n {
            Integral::Positive(n) => {
                if *n <= i64::MAX as u64 { Some(*n as i64) } else { None }
            }
            Integral::Negative(n) => Some(*n),
        }
    }

    pub fn as_u64(&self) -> Option<u64> {
        match &self.n {
            Integral::Positive(n) => Some(*n),
            Integral::Negative(_) => None,
        }
    }

    pub(crate) fn write_json(&self, out: &mut String) {
        match &self.n {
            Integral::Positive(n) => out.push_str(&n.to_string()),
            Integral::Negative(n) => out.push_str(&n.to_string()),
        }
    }
}

impl fmt::Debug for Number {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.n {
            Integral::Positive(n) => write!(f, "Number({})", n),
            Integral::Negative(n) => write!(f, "Number({})", n),
        }
    }
}

macro_rules! signed {
    ($($ty:ty),* $(,)?) => {$(
        impl From<$ty> for Number {
            fn from(n: $ty) -> Self {
                let n = n as i64;
                Self { n: if n < 0 { Integral::Negative(n) } else { Integral::Positive(n as u64) } }
            }
        }
    )*};
}
macro_rules! unsigned {
    ($($ty:ty),* $(,)?) => {$(
        impl From<$ty> for Number {
            fn from(n: $ty) -> Self { Self { n: Integral::Positive(n as u64) } }
        }
    )*};
}
signed!(i8, i16, i32, i64);
unsigned!(u8, u16, u32, u64);
// Never silently truncate a hypothetical wider pointer-sized input.
#[cfg(any(target_pointer_width = "16", target_pointer_width = "32", target_pointer_width = "64"))]
signed!(isize);
#[cfg(any(target_pointer_width = "16", target_pointer_width = "32", target_pointer_width = "64"))]
unsigned!(usize);
