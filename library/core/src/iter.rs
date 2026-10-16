// `core::iter` overlay (docs/ARCH.md section 3.1; W-STD-C): the source
// `once` and its iterator type `Once`.
// The other `core::iter` items (`repeat`, `empty`, `zip`, the adapters, the
// iterator traits) stay compiler-known; `std::iter::X` and `core::iter::X`
// walk into this module only for the names it defines (`STD_MODULES` in
// src/stdmods.rs).
//
// Lust std source, adapted from rust-lang/rust 1.99
// `core/src/iter/sources/once.rs`. Not here: `FusedIterator` and
// `TrustedLen` (lust has no such traits, so a bound on them rejects), and
// `once_with`, `from_fn`, `successors`: their `Iterator` impls carry a
// closure bound that mono cannot prove yet (`ensure_iter_methods`), so an
// adapter over one would fail in codegen; they stay L0505 rejects. `Once<T>` holds `Option<T>` where core holds an
// `option::IntoIter<T>`; its Debug text writes core's nesting by hand
// (`Once { inner: IntoIter { inner: Item { opt: Some(1) } } }`).

/// Creates an iterator that yields an element exactly once.
pub fn once<T>(value: T) -> Once<T> {
    Once { inner: Some(value) }
}

/// An iterator that yields an element exactly once (`once`).
#[derive(Clone)]
pub struct Once<T> {
    inner: Option<T>,
}

/// Debug of core's `option::Item { opt }` inside `option::IntoIter`.
struct OptionItemDebug<'a, T>(&'a Option<T>);

impl<T: core::fmt::Debug> core::fmt::Debug for OptionItemDebug<'_, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Item").field("opt", self.0).finish()
    }
}

/// Debug of core's `option::IntoIter { inner }`.
struct OptionIntoIterDebug<'a, T>(&'a Option<T>);

impl<T: core::fmt::Debug> core::fmt::Debug for OptionIntoIterDebug<'_, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("IntoIter").field("inner", &OptionItemDebug(self.0)).finish()
    }
}

impl<T: core::fmt::Debug> core::fmt::Debug for Once<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Once").field("inner", &OptionIntoIterDebug(&self.inner)).finish()
    }
}

impl<T> Iterator for Once<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.inner.take()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = if self.inner.is_some() { 1 } else { 0 };
        (len, Some(len))
    }
}

impl<T> DoubleEndedIterator for Once<T> {
    fn next_back(&mut self) -> Option<T> {
        self.inner.take()
    }
}

impl<T> ExactSizeIterator for Once<T> {
    fn len(&self) -> usize {
        if self.inner.is_some() { 1 } else { 0 }
    }
}
