//! JSON impls for `IndexMap` that must live in `goport_util`, the crate of
//! `MarshalerTo` and `UnmarshalerFrom` (orphan rule): the decode of Go
//! `collections.OrderedMap`, and the `JsonMapKey` bridge for map key types
//! of the crates above.

use crate::indexmap::IndexMap;

// Go: collections/ordered_map.go:263 (*OrderedMap).UnmarshalJSONFrom
// PORT: Go `collections.OrderedMap` is `IndexMap`. `IndexMap::insert` keeps
// the first position and replaces the value, like `OrderedMap.Set`.



