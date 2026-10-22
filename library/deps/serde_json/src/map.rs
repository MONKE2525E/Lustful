use crate::Value;
use std::collections::{btree_map, BTreeMap};
use std::fmt;

pub struct Map<K, V> {
    inner: BTreeMap<K, V>,
}

impl Map<String, Value> {
    pub fn new() -> Self { Self { inner: BTreeMap::new() } }
    pub fn len(&self) -> usize { self.inner.len() }
    pub fn is_empty(&self) -> bool { self.inner.is_empty() }
    pub fn insert(&mut self, key: String, value: Value) -> Option<Value> {
        self.inner.insert(key, value)
    }
    pub fn get(&self, key: &str) -> Option<&Value> { self.inner.get(key) }
    pub fn get_mut(&mut self, key: &str) -> Option<&mut Value> { self.inner.get_mut(key) }
    pub fn iter(&self) -> btree_map::Iter<'_, String, Value> { self.inner.iter() }
}
impl Default for Map<String, Value> {
    fn default() -> Self { Self::new() }
}
impl Clone for Map<String, Value> {
    fn clone(&self) -> Self { Self { inner: self.inner.clone() } }
}
impl PartialEq for Map<String, Value> {
    fn eq(&self, other: &Self) -> bool { self.inner == other.inner }
}
impl fmt::Debug for Map<String, Value> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.inner, f)
    }
}
