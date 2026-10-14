// `std::sync` overlay (docs/ARCH.md section 3.1; W-STD-C): `LazyLock`.
// `OnceLock`, `Arc`, `Mutex`, and the other `sync` items stay compiler-
// known (W-THREADS, thread-safe); `std::sync::X` walks into this module
// only for the names it defines (`STD_MODULES` in src/stdmods.rs).
//
// Lust std source, adapted from rust-lang/rust 1.99
// `std/src/sync/lazy_lock.rs`. The value lives in W-THREADS's
// `OnceLock<T>`, so first access is thread-safe: `get_or_init` runs the
// init closure exactly once, and only that closure takes `F` out of
// `init` (through the privileged `core::intrinsics::once_take`), so the
// take never races. Not modeled: `LazyLock: Sync` is structural here
// (`OnceLock<T>: Sync` and `F: Sync`), where std asks `F: Send`.

/// Debug text of an empty lock: `<uninit>`.
struct Uninit;

impl core::fmt::Debug for Uninit {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("<uninit>")
    }
}

/// A value initialized on first access by `F`.
pub struct LazyLock<T, F = fn() -> T> {
    once: std::sync::OnceLock<T>,
    init: Option<F>,
}

impl<T, F: FnOnce() -> T> LazyLock<T, F> {
    pub const fn new(f: F) -> LazyLock<T, F> {
        LazyLock { once: std::sync::OnceLock::new(), init: Some(f) }
    }

    pub fn force(this: &LazyLock<T, F>) -> &T {
        this.once.get_or_init(|| match core::intrinsics::once_take(&this.init) {
            Some(f) => f(),
            None => panic!("LazyLock instance has previously been poisoned"),
        })
    }

    pub fn force_mut(this: &mut LazyLock<T, F>) -> &mut T {
        LazyLock::force(this);
        match this.once.get_mut() {
            Some(v) => v,
            None => unreachable!(),
        }
    }

    pub fn get(this: &LazyLock<T, F>) -> Option<&T> {
        this.once.get()
    }

    pub fn get_mut(this: &mut LazyLock<T, F>) -> Option<&mut T> {
        this.once.get_mut()
    }
}

impl<T, F: FnOnce() -> T> core::ops::Deref for LazyLock<T, F> {
    type Target = T;
    fn deref(&self) -> &T {
        LazyLock::force(self)
    }
}

impl<T, F> From<T> for LazyLock<T, F> {
    fn from(value: T) -> LazyLock<T, F> {
        LazyLock { once: std::sync::OnceLock::from(value), init: None }
    }
}

impl<T: core::fmt::Debug, F> core::fmt::Debug for LazyLock<T, F> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut d = f.debug_tuple("LazyLock");
        match self.once.get() {
            Some(v) => d.field(v),
            None => d.field(&Uninit),
        };
        d.finish()
    }
}
