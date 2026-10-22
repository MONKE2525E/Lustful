use std::fmt;

#[derive(Clone, PartialEq)]
enum Repr {
    Positive(u64),
    Negative(i64),
    Float(f64),
}

#[derive(Clone, PartialEq)]
pub struct Number {
    n: Repr,
}

// Float is private and only constructed by the finite-result parser path.
impl Eq for Number {}

impl Number {
    pub fn is_i64(&self) -> bool { self.as_i64().is_some() }
    pub fn is_u64(&self) -> bool { self.as_u64().is_some() }
    pub fn is_f64(&self) -> bool { matches!(self.n, Repr::Float(_)) }
    pub fn as_i64(&self) -> Option<i64> {
        match &self.n {
            Repr::Positive(n) => {
                if *n <= i64::MAX as u64 { Some(*n as i64) } else { None }
            }
            Repr::Negative(n) => Some(*n),
            Repr::Float(_) => None,
        }
    }
    pub fn as_u64(&self) -> Option<u64> {
        match &self.n {
            Repr::Positive(n) => Some(*n),
            Repr::Negative(_) | Repr::Float(_) => None,
        }
    }
    pub fn as_f64(&self) -> Option<f64> {
        Some(match &self.n {
            Repr::Positive(n) => *n as f64,
            Repr::Negative(n) => *n as f64,
            Repr::Float(n) => *n,
        })
    }

    // Not a public float constructor. Caller is the default numeric parser.
    pub(crate) fn parsed_float(n: f64) -> Self { Self { n: Repr::Float(n) } }

    pub(crate) fn write_json(&self, out: &mut String) {
        match &self.n {
            Repr::Positive(n) => out.push_str(&n.to_string()),
            Repr::Negative(n) => out.push_str(&n.to_string()),
            Repr::Float(n) => crate::float_format::write_finite_f64(*n, out),
        }
    }
}

impl fmt::Display for Number {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut out = String::new();
        self.write_json(&mut out);
        f.write_str(&out)
    }
}
impl fmt::Debug for Number {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Number({})", self)
    }
}

macro_rules! signed {
    ($($ty:ty),* $(,)?) => {$(
        impl From<$ty> for Number {
            fn from(n: $ty) -> Self {
                let n = n as i64;
                Self { n: if n < 0 { Repr::Negative(n) } else { Repr::Positive(n as u64) } }
            }
        }
    )*};
}
macro_rules! unsigned {
    ($($ty:ty),* $(,)?) => {$(
        impl From<$ty> for Number {
            fn from(n: $ty) -> Self { Self { n: Repr::Positive(n as u64) } }
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
