use crate::{Map, Number};
use std::fmt;

#[derive(Clone, PartialEq)]
pub enum Value {
    Null,
    Bool(bool),
    Number(Number),
    String(String),
    Array(Vec<Value>),
    Object(Map<String, Value>),
}

impl Default for Value {
    fn default() -> Self { Self::Null }
}

impl Value {
    pub fn is_null(&self) -> bool { self.as_null().is_some() }
    pub fn is_boolean(&self) -> bool { self.as_bool().is_some() }
    pub fn is_string(&self) -> bool { self.as_str().is_some() }
    pub fn is_number(&self) -> bool { matches!(self, Self::Number(_)) }
    pub fn is_array(&self) -> bool { self.as_array().is_some() }
    pub fn is_object(&self) -> bool { self.as_object().is_some() }
    pub fn as_null(&self) -> Option<()> {
        match self { Self::Null => Some(()), _ => None }
    }
    pub fn as_bool(&self) -> Option<bool> {
        match self { Self::Bool(v) => Some(*v), _ => None }
    }
    pub fn as_str(&self) -> Option<&str> {
        match self { Self::String(v) => Some(v.as_str()), _ => None }
    }
    pub fn as_i64(&self) -> Option<i64> {
        match self { Self::Number(v) => v.as_i64(), _ => None }
    }
    pub fn as_u64(&self) -> Option<u64> {
        match self { Self::Number(v) => v.as_u64(), _ => None }
    }
    pub fn as_array(&self) -> Option<&Vec<Value>> {
        match self { Self::Array(v) => Some(v), _ => None }
    }
    pub fn as_array_mut(&mut self) -> Option<&mut Vec<Value>> {
        match self { Self::Array(v) => Some(v), _ => None }
    }
    pub fn as_object(&self) -> Option<&Map<String, Value>> {
        match self { Self::Object(v) => Some(v), _ => None }
    }
    pub fn as_object_mut(&mut self) -> Option<&mut Map<String, Value>> {
        match self { Self::Object(v) => Some(v), _ => None }
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Null => f.write_str("Null"),
            Self::Bool(v) => write!(f, "Bool({})", v),
            Self::Number(v) => fmt::Debug::fmt(v, f),
            Self::String(v) => write!(f, "String({:?})", v),
            Self::Array(v) => {
                f.write_str("Array ")?;
                fmt::Debug::fmt(v, f)
            }
            Self::Object(v) => {
                f.write_str("Object ")?;
                fmt::Debug::fmt(v, f)
            }
        }
    }
}
