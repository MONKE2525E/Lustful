// `std::sync` overlay (docs/ARCH.md section 3.1; W-STD-C): `OnceLock`
// and `LazyLock`. `Arc`, `Mutex`, and the other `sync` items stay
// compiler-known (or W-THREADS'); `std::sync::X` walks into this module
// only for the names it defines (`STD_MODULES` in src/stdmods.rs).
//
// Lust std source, adapted from rust-lang/rust 1.99
// `std/src/sync/once_lock.rs` and `std/src/sync/lazy_lock.rs`, with
// single-threaded semantics (thread safety is W-THREADS): the value is
// a plain `Option<T>` written through `&self` only by the privileged
// `core::intrinsics::once_init` and `once_take` builtins. The marker
// makes the locks invariant in `T`, as std's. Not modeled yet: the
// `T: Send` part of `OnceLock<T>: Sync`, and blocking in `wait`.

/// Debug text of an empty lock: `<uninit>`.
struct Uninit;

impl core::fmt::Debug for Uninit {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("<uninit>")
    }
}

/// A synchronization primitive that can be written to only once.
pub struct OnceLock<T> {
    inner: Option<T>,
    _marker: core::marker::PhantomData<fn(T) -> T>,
}

impl<T> OnceLock<T> {
    pub const fn new() -> OnceLock<T> {
        OnceLock { inner: None, _marker: core::marker::PhantomData }
    }

    pub fn get(&self) -> Option<&T> {
        match &self.inner {
            Some(v) => Some(v),
            None => None,
        }
    }

    pub fn get_mut(&mut self) -> Option<&mut T> {
        match &mut self.inner {
            Some(v) => Some(v),
            None => None,
        }
    }

    /// Single-threaded, nothing else can initialize the lock: an empty
    /// lock blocks forever, as std's does with no other thread.
    pub fn wait(&self) -> &T {
        loop {
            if let Some(v) = &self.inner {
                return v;
            }
        }
    }

    pub fn set(&self, value: T) -> Result<(), T> {
        if self.inner.is_some() {
            return Err(value);
        }
        core::intrinsics::once_init(&self.inner, value);
        Ok(())
    }

    pub fn get_or_init<F: FnOnce() -> T>(&self, f: F) -> &T {
        if self.inner.is_none() {
            let value = f();
            if self.inner.is_none() {
                core::intrinsics::once_init(&self.inner, value);
            }
        }
        match &self.inner {
            Some(v) => v,
            None => unreachable!(),
        }
    }

    pub fn into_inner(self) -> Option<T> {
        self.inner
    }

    pub fn take(&mut self) -> Option<T> {
        core::mem::replace(&mut self.inner, None)
    }
}

impl<T> Default for OnceLock<T> {
    fn default() -> OnceLock<T> {
        OnceLock::new()
    }
}

impl<T: core::fmt::Debug> core::fmt::Debug for OnceLock<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut d = f.debug_tuple("OnceLock");
        match &self.inner {
            Some(v) => d.field(v),
            None => d.field(&Uninit),
        };
        d.finish()
    }
}

impl<T: Clone> Clone for OnceLock<T> {
    fn clone(&self) -> OnceLock<T> {
        match &self.inner {
            Some(v) => OnceLock { inner: Some(v.clone()), _marker: core::marker::PhantomData },
            None => OnceLock::new(),
        }
    }
}

impl<T: PartialEq> PartialEq for OnceLock<T> {
    fn eq(&self, other: &OnceLock<T>) -> bool {
        match (&self.inner, &other.inner) {
            (Some(a), Some(b)) => *a == *b,
            (None, None) => true,
            _ => false,
        }
    }
}

impl<T: Eq> Eq for OnceLock<T> {}

impl<T> From<T> for OnceLock<T> {
    fn from(value: T) -> OnceLock<T> {
        OnceLock { inner: Some(value), _marker: core::marker::PhantomData }
    }
}

/// A value initialized on first access by `F`.
pub struct LazyLock<T, F = fn() -> T> {
    once: OnceLock<T>,
    init: Option<F>,
}

impl<T, F: FnOnce() -> T> LazyLock<T, F> {
    pub const fn new(f: F) -> LazyLock<T, F> {
        LazyLock { once: OnceLock::new(), init: Some(f) }
    }

    pub fn force(this: &LazyLock<T, F>) -> &T {
        if this.once.inner.is_none() {
            match core::intrinsics::once_take(&this.init) {
                Some(f) => {
                    let value = f();
                    core::intrinsics::once_init(&this.once.inner, value);
                }
                None => panic!("LazyLock instance has previously been poisoned"),
            }
        }
        match &this.once.inner {
            Some(v) => v,
            None => unreachable!(),
        }
    }

    pub fn force_mut(this: &mut LazyLock<T, F>) -> &mut T {
        if this.once.inner.is_none() {
            match core::intrinsics::once_take(&this.init) {
                Some(f) => {
                    let value = f();
                    core::intrinsics::once_init(&this.once.inner, value);
                }
                None => panic!("LazyLock instance has previously been poisoned"),
            }
        }
        match &mut this.once.inner {
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
        LazyLock { once: OnceLock { inner: Some(value), _marker: core::marker::PhantomData }, init: None }
    }
}

impl<T: core::fmt::Debug, F> core::fmt::Debug for LazyLock<T, F> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut d = f.debug_tuple("LazyLock");
        match &self.once.inner {
            Some(v) => d.field(v),
            None => d.field(&Uninit),
        };
        d.finish()
    }
}
