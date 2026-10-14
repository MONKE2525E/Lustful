// `alloc::collections` overlay (docs/ARCH.md section 3.1; W-STD-C):
// `BTreeMap`, `BTreeSet`, `VecDeque`, and their modules `btree_map`,
// `btree_set`, `vec_deque`. `HashMap` and `HashSet` stay W-STD-B's;
// `std::collections::X` and `alloc::collections::X` walk into this
// module only for the names it defines (`STD_MODULES` in
// src/stdmods.rs).
//
// Lust std source with std's observable behavior, not std's data
// structures:
// - `BTreeMap` and `BTreeSet` keep their entries sorted in one `Vec`
//   (binary search; O(n) insert and remove). Iteration order, drop
//   order (ascending keys, key before value), which key an insert of
//   an existing key keeps (the old one), and every return value are
//   std's.
// - `VecDeque` keeps its elements in logical order in one `Vec`, which
//   grows by the same RawVec rule, so `capacity()` matches. Methods
//   whose result depends on std's ring layout (`as_slices`,
//   `make_contiguous`, `rotate_*`) are not here.
// - The iterator types are aliases of the builtin adapters
//   (`Map<slice::Iter<'a, (K, V)>, fn(&(K, V)) -> (&K, &V)>` and kin), so
//   the whole adapter set works on them, with std's item types. They
//   have no `Debug` (std's prints the remaining items).
// Not here yet: `Extend` impls (the `Extend` trait is not on next yet),
// `VecDeque`'s `FromIterator` (its capacity
// follows `Vec`'s collect rules, which generic source cannot call yet), `range`, `Index` (`map[&k]` needs user `Index`), `Hash`,
// `From<[_; N]>`, the cursor and `extract_if` APIs, `DoubleEndedIterator`
// for the `Map` aliases beyond what the builtin adapters provide.

// The three types are defined here, not only re-exported, so a user
// `use std::collections::X` finds them while the overlay's own imports
// are still resolving; their modules re-export them.

/// An ordered map: entries sorted by key.
pub struct BTreeMap<K, V> {
    entries: Vec<(K, V)>,
}

/// An ordered set: elements sorted, no duplicates.
pub struct BTreeSet<T> {
    items: Vec<T>,
}

/// A double-ended queue.
pub struct VecDeque<T> {
    buf: Vec<T>,
}

/// The order of two keys. A `.cmp` call on a generic `Q` cannot be
/// instantiated for every `Q` yet (`&str`, tuples: the generic stub
/// pick), the comparison operators can. For the key types allowed here
/// (`Ord` consistent with `PartialOrd`, see the header) the answer is
/// `Ord::cmp`'s.
fn cmp_of<Q: ?Sized + Ord>(a: &Q, b: &Q) -> core::cmp::Ordering {
    if a < b {
        core::cmp::Ordering::Less
    } else if a == b {
        core::cmp::Ordering::Equal
    } else {
        core::cmp::Ordering::Greater
    }
}

pub mod btree_map {
    use core::borrow::Borrow;

    pub use super::BTreeMap;

    pub type Iter<'a, K, V> = core::iter::Map<core::slice::Iter<'a, (K, V)>, fn(&(K, V)) -> (&K, &V)>;
    pub type IterMut<'a, K, V> = core::iter::Map<core::slice::IterMut<'a, (K, V)>, fn(&mut (K, V)) -> (&K, &mut V)>;
    pub type Keys<'a, K, V> = core::iter::Map<core::slice::Iter<'a, (K, V)>, fn(&(K, V)) -> &K>;
    pub type Values<'a, K, V> = core::iter::Map<core::slice::Iter<'a, (K, V)>, fn(&(K, V)) -> &V>;
    pub type ValuesMut<'a, K, V> = core::iter::Map<core::slice::IterMut<'a, (K, V)>, fn(&mut (K, V)) -> &mut V>;
    pub type IntoIter<K, V> = std::vec::IntoIter<(K, V)>;
    pub type IntoKeys<K, V> = core::iter::Map<std::vec::IntoIter<(K, V)>, fn((K, V)) -> K>;
    pub type IntoValues<K, V> = core::iter::Map<std::vec::IntoIter<(K, V)>, fn((K, V)) -> V>;

    fn pair_ref<K, V>(p: &(K, V)) -> (&K, &V) {
        (&p.0, &p.1)
    }

    fn pair_mut<K, V>(p: &mut (K, V)) -> (&K, &mut V) {
        (&p.0, &mut p.1)
    }

    fn key_ref<K, V>(p: &(K, V)) -> &K {
        &p.0
    }

    fn value_ref<K, V>(p: &(K, V)) -> &V {
        &p.1
    }

    fn value_mut<K, V>(p: &mut (K, V)) -> &mut V {
        &mut p.1
    }

    fn into_key<K, V>(p: (K, V)) -> K {
        p.0
    }

    fn into_value<K, V>(p: (K, V)) -> V {
        p.1
    }

    impl<K, V> BTreeMap<K, V> {
        pub const fn new() -> BTreeMap<K, V> {
            BTreeMap { entries: Vec::new() }
        }

        pub fn len(&self) -> usize {
            self.entries.len()
        }

        pub fn is_empty(&self) -> bool {
            self.entries.is_empty()
        }

        pub fn clear(&mut self) {
            self.entries.clear();
        }

        pub fn iter(&self) -> Iter<'_, K, V> {
            self.entries.iter().map(pair_ref as fn(&(K, V)) -> (&K, &V))
        }

        pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
            self.entries.iter_mut().map(pair_mut as fn(&mut (K, V)) -> (&K, &mut V))
        }

        pub fn keys(&self) -> Keys<'_, K, V> {
            self.entries.iter().map(key_ref as fn(&(K, V)) -> &K)
        }

        pub fn values(&self) -> Values<'_, K, V> {
            self.entries.iter().map(value_ref as fn(&(K, V)) -> &V)
        }

        pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
            self.entries.iter_mut().map(value_mut as fn(&mut (K, V)) -> &mut V)
        }

        pub fn into_keys(self) -> IntoKeys<K, V> {
            self.entries.into_iter().map(into_key as fn((K, V)) -> K)
        }

        pub fn into_values(self) -> IntoValues<K, V> {
            self.entries.into_iter().map(into_value as fn((K, V)) -> V)
        }

        pub fn first_key_value(&self) -> Option<(&K, &V)> {
            match self.entries.first() {
                Some(p) => Some((&p.0, &p.1)),
                None => None,
            }
        }

        pub fn last_key_value(&self) -> Option<(&K, &V)> {
            match self.entries.last() {
                Some(p) => Some((&p.0, &p.1)),
                None => None,
            }
        }

        pub fn pop_first(&mut self) -> Option<(K, V)> {
            if self.entries.is_empty() { None } else { Some(self.entries.remove(0)) }
        }

        pub fn pop_last(&mut self) -> Option<(K, V)> {
            self.entries.pop()
        }

        pub fn retain<F: FnMut(&K, &mut V) -> bool>(&mut self, mut f: F) {
            let mut i = 0;
            while i < self.entries.len() {
                let keep = {
                    let p = &mut self.entries[i];
                    f(&p.0, &mut p.1)
                };
                if keep {
                    i += 1;
                } else {
                    self.entries.remove(i);
                }
            }
        }
    }

    impl<K: Ord, V> BTreeMap<K, V> {
        /// The index of `key`, or where it would go, by `K`'s own order.
        fn search_key(&self, key: &K) -> Result<usize, usize> {
            let mut lo = 0;
            let mut hi = self.entries.len();
            while lo < hi {
                let mid = lo + (hi - lo) / 2;
                match super::cmp_of(&self.entries[mid].0, key) {
                    core::cmp::Ordering::Less => lo = mid + 1,
                    core::cmp::Ordering::Greater => hi = mid,
                    core::cmp::Ordering::Equal => return Ok(mid),
                }
            }
            Err(lo)
        }

        /// The index of `key`, or where it would go, through `Borrow`.
        fn search<Q: ?Sized + Ord>(&self, key: &Q) -> Result<usize, usize>
        where
            K: Borrow<Q>,
        {
            let mut lo = 0;
            let mut hi = self.entries.len();
            while lo < hi {
                let mid = lo + (hi - lo) / 2;
                match super::cmp_of(self.entries[mid].0.borrow(), key) {
                    core::cmp::Ordering::Less => lo = mid + 1,
                    core::cmp::Ordering::Greater => hi = mid,
                    core::cmp::Ordering::Equal => return Ok(mid),
                }
            }
            Err(lo)
        }

        pub fn insert(&mut self, key: K, value: V) -> Option<V> {
            match self.search_key(&key) {
                Ok(i) => Some(core::mem::replace(&mut self.entries[i].1, value)),
                Err(i) => {
                    self.entries.insert(i, (key, value));
                    None
                }
            }
        }

        pub fn get<Q: ?Sized + Ord>(&self, key: &Q) -> Option<&V>
        where
            K: Borrow<Q>,
        {
            match self.search(key) {
                Ok(i) => Some(&self.entries[i].1),
                Err(_) => None,
            }
        }

        pub fn get_key_value<Q: ?Sized + Ord>(&self, key: &Q) -> Option<(&K, &V)>
        where
            K: Borrow<Q>,
        {
            match self.search(key) {
                Ok(i) => Some((&self.entries[i].0, &self.entries[i].1)),
                Err(_) => None,
            }
        }

        pub fn get_mut<Q: ?Sized + Ord>(&mut self, key: &Q) -> Option<&mut V>
        where
            K: Borrow<Q>,
        {
            match self.search(key) {
                Ok(i) => Some(&mut self.entries[i].1),
                Err(_) => None,
            }
        }

        pub fn contains_key<Q: ?Sized + Ord>(&self, key: &Q) -> bool
        where
            K: Borrow<Q>,
        {
            match self.search(key) {
                Ok(_) => true,
                Err(_) => false,
            }
        }

        pub fn remove<Q: ?Sized + Ord>(&mut self, key: &Q) -> Option<V>
        where
            K: Borrow<Q>,
        {
            match self.search(key) {
                Ok(i) => Some(self.entries.remove(i).1),
                Err(_) => None,
            }
        }

        pub fn remove_entry<Q: ?Sized + Ord>(&mut self, key: &Q) -> Option<(K, V)>
        where
            K: Borrow<Q>,
        {
            match self.search(key) {
                Ok(i) => Some(self.entries.remove(i)),
                Err(_) => None,
            }
        }

        pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
            match self.search_key(&key) {
                Ok(index) => Entry::Occupied(OccupiedEntry { map: self, index }),
                Err(index) => Entry::Vacant(VacantEntry { map: self, key, index }),
            }
        }

        /// Moves every entry of `other` in. On an equal key `other`'s whole
        /// entry stays and this map's drops, as std's merge does.
        pub fn append(&mut self, other: &mut BTreeMap<K, V>) {
            if other.entries.is_empty() {
                return;
            }
            if self.entries.is_empty() {
                core::mem::swap(&mut self.entries, &mut other.entries);
                return;
            }
            let left = core::mem::replace(&mut self.entries, Vec::new());
            let right = core::mem::replace(&mut other.entries, Vec::new());
            let mut out: Vec<(K, V)> = Vec::new();
            let mut a = left.into_iter();
            let mut b = right.into_iter();
            let mut na = a.next();
            let mut nb = b.next();
            loop {
                let ord = if let Some(x) = &na {
                    if let Some(y) = &nb { super::cmp_of(&x.0, &y.0) } else { core::cmp::Ordering::Less }
                } else if nb.is_some() {
                    core::cmp::Ordering::Greater
                } else {
                    break
                };
                match ord {
                    core::cmp::Ordering::Less => {
                        out.push(core::mem::replace(&mut na, None).unwrap());
                        na = a.next();
                    }
                    core::cmp::Ordering::Greater => {
                        out.push(core::mem::replace(&mut nb, None).unwrap());
                        nb = b.next();
                    }
                    core::cmp::Ordering::Equal => {
                        let dropped = core::mem::replace(&mut na, None);
                        drop(dropped);
                        out.push(core::mem::replace(&mut nb, None).unwrap());
                        na = a.next();
                        nb = b.next();
                    }
                }
            }
            self.entries = out;
        }

        /// Splits off the entries with keys at or above `key`.
        pub fn split_off<Q: ?Sized + Ord>(&mut self, key: &Q) -> BTreeMap<K, V>
        where
            K: Borrow<Q>,
        {
            let at = match self.search(key) {
                Ok(i) => i,
                Err(i) => i,
            };
            BTreeMap { entries: self.entries.split_off(at) }
        }
    }

    /// A view into one entry of a map.
    pub enum Entry<'a, K, V> {
        Vacant(VacantEntry<'a, K, V>),
        Occupied(OccupiedEntry<'a, K, V>),
    }

    /// An entry whose key is not in the map.
    pub struct VacantEntry<'a, K, V> {
        map: &'a mut BTreeMap<K, V>,
        key: K,
        index: usize,
    }

    /// An entry whose key is in the map.
    pub struct OccupiedEntry<'a, K, V> {
        map: &'a mut BTreeMap<K, V>,
        index: usize,
    }

    impl<'a, K: Ord, V> Entry<'a, K, V> {
        pub fn or_insert(self, default: V) -> &'a mut V {
            match self {
                Entry::Occupied(e) => e.into_mut(),
                Entry::Vacant(e) => e.insert(default),
            }
        }

        pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
            match self {
                Entry::Occupied(e) => e.into_mut(),
                Entry::Vacant(e) => e.insert(default()),
            }
        }

        pub fn or_insert_with_key<F: FnOnce(&K) -> V>(self, default: F) -> &'a mut V {
            match self {
                Entry::Occupied(e) => e.into_mut(),
                Entry::Vacant(e) => {
                    let value = default(&e.key);
                    e.insert(value)
                }
            }
        }

        pub fn key(&self) -> &K {
            match self {
                Entry::Occupied(e) => e.key(),
                Entry::Vacant(e) => e.key(),
            }
        }

        pub fn and_modify<F: FnOnce(&mut V)>(self, f: F) -> Entry<'a, K, V> {
            match self {
                Entry::Occupied(mut e) => {
                    f(e.get_mut());
                    Entry::Occupied(e)
                }
                Entry::Vacant(e) => Entry::Vacant(e),
            }
        }
    }

    impl<'a, K: Ord, V: Default> Entry<'a, K, V> {
        pub fn or_default(self) -> &'a mut V {
            match self {
                Entry::Occupied(e) => e.into_mut(),
                Entry::Vacant(e) => e.insert(V::default()),
            }
        }
    }

    impl<'a, K: Ord, V> VacantEntry<'a, K, V> {
        pub fn key(&self) -> &K {
            &self.key
        }

        pub fn into_key(self) -> K {
            self.key
        }

        pub fn insert(self, value: V) -> &'a mut V {
            let index = self.index;
            let map = self.map;
            map.entries.insert(index, (self.key, value));
            &mut map.entries[index].1
        }
    }

    impl<'a, K: Ord, V> OccupiedEntry<'a, K, V> {
        pub fn key(&self) -> &K {
            &self.map.entries[self.index].0
        }

        pub fn get(&self) -> &V {
            &self.map.entries[self.index].1
        }

        pub fn get_mut(&mut self) -> &mut V {
            &mut self.map.entries[self.index].1
        }

        pub fn into_mut(self) -> &'a mut V {
            let index = self.index;
            &mut self.map.entries[index].1
        }

        pub fn insert(&mut self, value: V) -> V {
            core::mem::replace(&mut self.map.entries[self.index].1, value)
        }

        pub fn remove(self) -> V {
            self.map.entries.remove(self.index).1
        }

        pub fn remove_entry(self) -> (K, V) {
            self.map.entries.remove(self.index)
        }
    }

    impl<K, V> Default for BTreeMap<K, V> {
        fn default() -> BTreeMap<K, V> {
            BTreeMap::new()
        }
    }

    impl<K: Clone, V: Clone> Clone for BTreeMap<K, V> {
        fn clone(&self) -> BTreeMap<K, V> {
            BTreeMap { entries: self.entries.clone() }
        }
    }

    impl<K: PartialEq, V: PartialEq> PartialEq for BTreeMap<K, V> {
        fn eq(&self, other: &BTreeMap<K, V>) -> bool {
            self.entries == other.entries
        }
    }

    impl<K: Eq, V: Eq> Eq for BTreeMap<K, V> {}

    impl<K: core::fmt::Debug, V: core::fmt::Debug> core::fmt::Debug for BTreeMap<K, V> {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            let mut m = f.debug_map();
            for p in &self.entries {
                m.entry(&p.0, &p.1);
            }
            m.finish()
        }
    }

    /// Std's bulk build: a stable sort by key, then the last of each run
    /// of equal keys stays (the earlier ones drop in order), as
    /// `DedupSortedIter` does.
    fn sorted_dedup_last<K: Ord, V>(mut items: Vec<(K, V)>) -> Vec<(K, V)> {
        use super::cmp_of;
        // Stable insertion sort (comparisons are unobservable: keys
        // reaching a written Ord impl reject at check, see the header).
        let mut i = 1;
        while i < items.len() {
            let mut j = i;
            while j > 0 && cmp_of(&items[j - 1].0, &items[j].0) == core::cmp::Ordering::Greater {
                items.swap(j - 1, j);
                j -= 1;
            }
            i += 1;
        }
        let mut out: Vec<(K, V)> = Vec::new();
        for item in items {
            let dup = match out.last() {
                Some(last) => cmp_of(&last.0, &item.0) == core::cmp::Ordering::Equal,
                None => false,
            };
            if dup {
                out.pop();
            }
            out.push(item);
        }
        out
    }

    impl<K: Ord, V> FromIterator<(K, V)> for BTreeMap<K, V> {
        fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> BTreeMap<K, V> {
            let mut items: Vec<(K, V)> = Vec::new();
            for kv in iter {
                items.push(kv);
            }
            BTreeMap { entries: sorted_dedup_last(items) }
        }
    }

    impl<K, V> IntoIterator for BTreeMap<K, V> {
        type Item = (K, V);
        type IntoIter = IntoIter<K, V>;
        fn into_iter(self) -> IntoIter<K, V> {
            self.entries.into_iter()
        }
    }

    impl<'a, K, V> IntoIterator for &'a BTreeMap<K, V> {
        type Item = (&'a K, &'a V);
        type IntoIter = Iter<'a, K, V>;
        fn into_iter(self) -> Iter<'a, K, V> {
            self.iter()
        }
    }

    impl<'a, K, V> IntoIterator for &'a mut BTreeMap<K, V> {
        type Item = (&'a K, &'a mut V);
        type IntoIter = IterMut<'a, K, V>;
        fn into_iter(self) -> IterMut<'a, K, V> {
            self.iter_mut()
        }
    }
}

pub mod btree_set {
    use core::borrow::Borrow;

    pub use super::BTreeSet;

    pub type Iter<'a, T> = core::slice::Iter<'a, T>;
    pub type IntoIter<T> = std::vec::IntoIter<T>;

    impl<T> BTreeSet<T> {
        pub const fn new() -> BTreeSet<T> {
            BTreeSet { items: Vec::new() }
        }

        pub fn len(&self) -> usize {
            self.items.len()
        }

        pub fn is_empty(&self) -> bool {
            self.items.is_empty()
        }

        pub fn clear(&mut self) {
            self.items.clear();
        }

        pub fn iter(&self) -> Iter<'_, T> {
            self.items.iter()
        }

        pub fn first(&self) -> Option<&T> {
            self.items.first()
        }

        pub fn last(&self) -> Option<&T> {
            self.items.last()
        }

        pub fn pop_first(&mut self) -> Option<T> {
            if self.items.is_empty() { None } else { Some(self.items.remove(0)) }
        }

        pub fn pop_last(&mut self) -> Option<T> {
            self.items.pop()
        }

        pub fn retain<F: FnMut(&T) -> bool>(&mut self, mut f: F) {
            let mut i = 0;
            while i < self.items.len() {
                if f(&self.items[i]) {
                    i += 1;
                } else {
                    self.items.remove(i);
                }
            }
        }
    }

    impl<T: Ord> BTreeSet<T> {
        /// The index of `value`, or where it would go, by `T`'s own order.
        fn search_key(&self, value: &T) -> Result<usize, usize> {
            let mut lo = 0;
            let mut hi = self.items.len();
            while lo < hi {
                let mid = lo + (hi - lo) / 2;
                match super::cmp_of(&self.items[mid], value) {
                    core::cmp::Ordering::Less => lo = mid + 1,
                    core::cmp::Ordering::Greater => hi = mid,
                    core::cmp::Ordering::Equal => return Ok(mid),
                }
            }
            Err(lo)
        }

        fn search<Q: ?Sized + Ord>(&self, value: &Q) -> Result<usize, usize>
        where
            T: Borrow<Q>,
        {
            let mut lo = 0;
            let mut hi = self.items.len();
            while lo < hi {
                let mid = lo + (hi - lo) / 2;
                match super::cmp_of(self.items[mid].borrow(), value) {
                    core::cmp::Ordering::Less => lo = mid + 1,
                    core::cmp::Ordering::Greater => hi = mid,
                    core::cmp::Ordering::Equal => return Ok(mid),
                }
            }
            Err(lo)
        }

        /// Adds `value`; false (and `value` dropped) when an equal one is
        /// already there, which stays.
        pub fn insert(&mut self, value: T) -> bool {
            match self.search_key(&value) {
                Ok(_) => false,
                Err(i) => {
                    self.items.insert(i, value);
                    true
                }
            }
        }

        /// Adds `value`, replacing and returning an equal one.
        pub fn replace(&mut self, value: T) -> Option<T> {
            match self.search_key(&value) {
                Ok(i) => Some(core::mem::replace(&mut self.items[i], value)),
                Err(i) => {
                    self.items.insert(i, value);
                    None
                }
            }
        }

        pub fn contains<Q: ?Sized + Ord>(&self, value: &Q) -> bool
        where
            T: Borrow<Q>,
        {
            match self.search(value) {
                Ok(_) => true,
                Err(_) => false,
            }
        }

        pub fn get<Q: ?Sized + Ord>(&self, value: &Q) -> Option<&T>
        where
            T: Borrow<Q>,
        {
            match self.search(value) {
                Ok(i) => Some(&self.items[i]),
                Err(_) => None,
            }
        }

        pub fn remove<Q: ?Sized + Ord>(&mut self, value: &Q) -> bool
        where
            T: Borrow<Q>,
        {
            match self.search(value) {
                Ok(i) => {
                    self.items.remove(i);
                    true
                }
                Err(_) => false,
            }
        }

        pub fn take<Q: ?Sized + Ord>(&mut self, value: &Q) -> Option<T>
        where
            T: Borrow<Q>,
        {
            match self.search(value) {
                Ok(i) => Some(self.items.remove(i)),
                Err(_) => None,
            }
        }

        /// Std's merge: on an equal value `other`'s stays and this set's
        /// drops.
        pub fn append(&mut self, other: &mut BTreeSet<T>) {
            if other.items.is_empty() {
                return;
            }
            if self.items.is_empty() {
                core::mem::swap(&mut self.items, &mut other.items);
                return;
            }
            let left = core::mem::replace(&mut self.items, Vec::new());
            let right = core::mem::replace(&mut other.items, Vec::new());
            let mut out: Vec<T> = Vec::new();
            let mut a = left.into_iter();
            let mut b = right.into_iter();
            let mut na = a.next();
            let mut nb = b.next();
            loop {
                let ord = if let Some(x) = &na {
                    if let Some(y) = &nb { super::cmp_of(x, y) } else { core::cmp::Ordering::Less }
                } else if nb.is_some() {
                    core::cmp::Ordering::Greater
                } else {
                    break
                };
                match ord {
                    core::cmp::Ordering::Less => {
                        out.push(core::mem::replace(&mut na, None).unwrap());
                        na = a.next();
                    }
                    core::cmp::Ordering::Greater => {
                        out.push(core::mem::replace(&mut nb, None).unwrap());
                        nb = b.next();
                    }
                    core::cmp::Ordering::Equal => {
                        let dropped = core::mem::replace(&mut na, None);
                        drop(dropped);
                        out.push(core::mem::replace(&mut nb, None).unwrap());
                        na = a.next();
                        nb = b.next();
                    }
                }
            }
            self.items = out;
        }

        pub fn split_off<Q: ?Sized + Ord>(&mut self, value: &Q) -> BTreeSet<T>
        where
            T: Borrow<Q>,
        {
            let at = match self.search(value) {
                Ok(i) => i,
                Err(i) => i,
            };
            BTreeSet { items: self.items.split_off(at) }
        }

        pub fn is_subset(&self, other: &BTreeSet<T>) -> bool {
            for v in &self.items {
                if let Err(_) = other.search_key(v) {
                    return false;
                }
            }
            true
        }

        pub fn is_superset(&self, other: &BTreeSet<T>) -> bool {
            other.is_subset(self)
        }

        pub fn is_disjoint(&self, other: &BTreeSet<T>) -> bool {
            for v in &self.items {
                if let Ok(_) = other.search_key(v) {
                    return false;
                }
            }
            true
        }
    }

    impl<T> Default for BTreeSet<T> {
        fn default() -> BTreeSet<T> {
            BTreeSet::new()
        }
    }

    impl<T: Clone> Clone for BTreeSet<T> {
        fn clone(&self) -> BTreeSet<T> {
            BTreeSet { items: self.items.clone() }
        }
    }

    impl<T: PartialEq> PartialEq for BTreeSet<T> {
        fn eq(&self, other: &BTreeSet<T>) -> bool {
            self.items == other.items
        }
    }

    impl<T: Eq> Eq for BTreeSet<T> {}

    impl<T: core::fmt::Debug> core::fmt::Debug for BTreeSet<T> {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            let mut s = f.debug_set();
            for v in &self.items {
                s.entry(v);
            }
            s.finish()
        }
    }

    impl<T: Ord> FromIterator<T> for BTreeSet<T> {
        /// Std's bulk build: stable sort, the last of equal values stays.
        fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> BTreeSet<T> {
            let mut items: Vec<T> = Vec::new();
            for v in iter {
                items.push(v);
            }
            let mut i = 1;
            while i < items.len() {
                let mut j = i;
                while j > 0 && super::cmp_of(&items[j - 1], &items[j]) == core::cmp::Ordering::Greater {
                    items.swap(j - 1, j);
                    j -= 1;
                }
                i += 1;
            }
            let mut out: Vec<T> = Vec::new();
            for item in items {
                let dup = match out.last() {
                    Some(last) => super::cmp_of(last, &item) == core::cmp::Ordering::Equal,
                    None => false,
                };
                if dup {
                    out.pop();
                }
                out.push(item);
            }
            BTreeSet { items: out }
        }
    }

    impl<T> IntoIterator for BTreeSet<T> {
        type Item = T;
        type IntoIter = IntoIter<T>;
        fn into_iter(self) -> IntoIter<T> {
            self.items.into_iter()
        }
    }

    impl<'a, T> IntoIterator for &'a BTreeSet<T> {
        type Item = &'a T;
        type IntoIter = Iter<'a, T>;
        fn into_iter(self) -> Iter<'a, T> {
            self.items.iter()
        }
    }
}

pub mod vec_deque {
    pub use super::VecDeque;

    pub type Iter<'a, T> = core::slice::Iter<'a, T>;
    pub type IterMut<'a, T> = core::slice::IterMut<'a, T>;
    pub type IntoIter<T> = std::vec::IntoIter<T>;

    impl<T> VecDeque<T> {
        pub const fn new() -> VecDeque<T> {
            VecDeque { buf: Vec::new() }
        }

        pub fn with_capacity(capacity: usize) -> VecDeque<T> {
            VecDeque { buf: Vec::with_capacity(capacity) }
        }

        pub fn len(&self) -> usize {
            self.buf.len()
        }

        pub fn is_empty(&self) -> bool {
            self.buf.is_empty()
        }

        pub fn capacity(&self) -> usize {
            self.buf.capacity()
        }

        pub fn clear(&mut self) {
            self.buf.clear();
        }

        pub fn push_back(&mut self, value: T) {
            self.buf.push(value);
        }

        pub fn push_front(&mut self, value: T) {
            self.buf.insert(0, value);
        }

        pub fn pop_back(&mut self) -> Option<T> {
            self.buf.pop()
        }

        pub fn pop_front(&mut self) -> Option<T> {
            if self.buf.is_empty() { None } else { Some(self.buf.remove(0)) }
        }

        pub fn front(&self) -> Option<&T> {
            self.buf.first()
        }

        pub fn back(&self) -> Option<&T> {
            self.buf.last()
        }

        pub fn front_mut(&mut self) -> Option<&mut T> {
            self.buf.first_mut()
        }

        pub fn back_mut(&mut self) -> Option<&mut T> {
            self.buf.last_mut()
        }

        pub fn get(&self, index: usize) -> Option<&T> {
            self.buf.get(index)
        }

        pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
            self.buf.get_mut(index)
        }

        pub fn insert(&mut self, index: usize, value: T) {
            if index > self.buf.len() {
                panic!("index out of bounds");
            }
            self.buf.insert(index, value);
        }

        pub fn remove(&mut self, index: usize) -> Option<T> {
            if index < self.buf.len() { Some(self.buf.remove(index)) } else { None }
        }

        pub fn swap(&mut self, i: usize, j: usize) {
            self.buf.swap(i, j);
        }

        pub fn truncate(&mut self, len: usize) {
            self.buf.truncate(len);
        }

        pub fn reserve(&mut self, additional: usize) {
            self.buf.reserve(additional);
        }

        pub fn reserve_exact(&mut self, additional: usize) {
            self.buf.reserve_exact(additional);
        }

        pub fn shrink_to_fit(&mut self) {
            self.buf.shrink_to_fit();
        }

        pub fn iter(&self) -> Iter<'_, T> {
            self.buf.iter()
        }

        pub fn iter_mut(&mut self) -> IterMut<'_, T> {
            self.buf.iter_mut()
        }

        pub fn contains(&self, x: &T) -> bool
        where
            T: PartialEq,
        {
            self.buf.contains(x)
        }

        pub fn retain<F: FnMut(&T) -> bool>(&mut self, mut f: F) {
            let mut i = 0;
            while i < self.buf.len() {
                if f(&self.buf[i]) {
                    i += 1;
                } else {
                    self.buf.remove(i);
                }
            }
        }

        pub fn append(&mut self, other: &mut VecDeque<T>) {
            self.buf.append(&mut other.buf);
        }

        pub fn split_off(&mut self, at: usize) -> VecDeque<T> {
            VecDeque { buf: self.buf.split_off(at) }
        }

        pub fn swap_remove_back(&mut self, index: usize) -> Option<T> {
            if index < self.buf.len() { Some(self.buf.swap_remove(index)) } else { None }
        }
    }

    impl<T> Default for VecDeque<T> {
        fn default() -> VecDeque<T> {
            VecDeque::new()
        }
    }

    impl<T: Clone> Clone for VecDeque<T> {
        fn clone(&self) -> VecDeque<T> {
            VecDeque { buf: self.buf.clone() }
        }
    }

    impl<T: PartialEq> PartialEq for VecDeque<T> {
        fn eq(&self, other: &VecDeque<T>) -> bool {
            self.buf == other.buf
        }
    }

    impl<T: Eq> Eq for VecDeque<T> {}

    impl<T: core::fmt::Debug> core::fmt::Debug for VecDeque<T> {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            let mut l = f.debug_list();
            for v in &self.buf {
                l.entry(v);
            }
            l.finish()
        }
    }

    impl<T> From<Vec<T>> for VecDeque<T> {
        fn from(buf: Vec<T>) -> VecDeque<T> {
            VecDeque { buf }
        }
    }

    impl<T> IntoIterator for VecDeque<T> {
        type Item = T;
        type IntoIter = IntoIter<T>;
        fn into_iter(self) -> IntoIter<T> {
            self.buf.into_iter()
        }
    }

    impl<'a, T> IntoIterator for &'a VecDeque<T> {
        type Item = &'a T;
        type IntoIter = Iter<'a, T>;
        fn into_iter(self) -> Iter<'a, T> {
            self.buf.iter()
        }
    }

    impl<'a, T> IntoIterator for &'a mut VecDeque<T> {
        type Item = &'a mut T;
        type IntoIter = IterMut<'a, T>;
        fn into_iter(self) -> IterMut<'a, T> {
            self.buf.iter_mut()
        }
    }
}
