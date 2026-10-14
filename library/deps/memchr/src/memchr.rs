// Single-byte searches: one, two, or three needle bytes, forward and
// reverse, plus the double-ended iterators over all matches.

/// The first index of `needle` in `haystack`.
pub fn memchr(needle: u8, haystack: &[u8]) -> Option<usize> {
    memchr3_in(needle, needle, needle, haystack, 0, haystack.len())
}

/// The last index of `needle` in `haystack`.
pub fn memrchr(needle: u8, haystack: &[u8]) -> Option<usize> {
    memrchr3_in(needle, needle, needle, haystack, 0, haystack.len())
}

/// The first index of either needle byte.
pub fn memchr2(needle1: u8, needle2: u8, haystack: &[u8]) -> Option<usize> {
    memchr3_in(needle1, needle2, needle2, haystack, 0, haystack.len())
}

/// The last index of either needle byte.
pub fn memrchr2(needle1: u8, needle2: u8, haystack: &[u8]) -> Option<usize> {
    memrchr3_in(needle1, needle2, needle2, haystack, 0, haystack.len())
}

/// The first index of any of the three needle bytes.
pub fn memchr3(needle1: u8, needle2: u8, needle3: u8, haystack: &[u8]) -> Option<usize> {
    memchr3_in(needle1, needle2, needle3, haystack, 0, haystack.len())
}

/// The last index of any of the three needle bytes.
pub fn memrchr3(needle1: u8, needle2: u8, needle3: u8, haystack: &[u8]) -> Option<usize> {
    memrchr3_in(needle1, needle2, needle3, haystack, 0, haystack.len())
}

/// An iterator over every index of `needle`, front to back.
pub fn memchr_iter<'h>(needle: u8, haystack: &'h [u8]) -> Memchr<'h> {
    Memchr::new(needle, haystack)
}

/// An iterator over every index of either needle byte.
pub fn memchr2_iter<'h>(needle1: u8, needle2: u8, haystack: &'h [u8]) -> Memchr2<'h> {
    Memchr2::new(needle1, needle2, haystack)
}

/// An iterator over every index of any of the three needle bytes.
pub fn memchr3_iter<'h>(needle1: u8, needle2: u8, needle3: u8, haystack: &'h [u8]) -> Memchr3<'h> {
    Memchr3::new(needle1, needle2, needle3, haystack)
}

/// The first index in `start..end` holding one of the needles.
fn memchr3_in(n1: u8, n2: u8, n3: u8, haystack: &[u8], start: usize, end: usize) -> Option<usize> {
    let mut i = start;
    while i < end {
        let b = haystack[i];
        if b == n1 || b == n2 || b == n3 {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// The last index in `start..end` holding one of the needles.
fn memrchr3_in(n1: u8, n2: u8, n3: u8, haystack: &[u8], start: usize, end: usize) -> Option<usize> {
    let mut i = end;
    while i > start {
        i -= 1;
        let b = haystack[i];
        if b == n1 || b == n2 || b == n3 {
            return Some(i);
        }
    }
    None
}

/// Every index of one needle byte. The unsearched range is `start..end`;
/// a match moves `start` past it, as upstream's pointer pair does. `end`
/// is the hook for `next_back`. Upstream also overrides `size_hint` and
/// implements `DoubleEndedIterator`; lust's `Iterator` has neither yet,
/// so both reject at the call. Add them here when std gains them, or
/// `size_hint` answers (and collect capacities) go wrong
/// (tests/adapters/crates/memchr has the cases that catch it).
#[derive(Clone)]
pub struct Memchr<'h> {
    needle1: u8,
    haystack: &'h [u8],
    start: usize,
    end: usize,
}

impl<'h> Memchr<'h> {
    pub fn new(needle1: u8, haystack: &'h [u8]) -> Memchr<'h> {
        Memchr { needle1, haystack, start: 0, end: haystack.len() }
    }
}

impl<'h> Iterator for Memchr<'h> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        let n = self.needle1;
        let i = memchr3_in(n, n, n, self.haystack, self.start, self.end)?;
        self.start = i + 1;
        Some(i)
    }

}


/// Every index of either of two needle bytes. See `Memchr`.
#[derive(Clone)]
pub struct Memchr2<'h> {
    needle1: u8,
    needle2: u8,
    haystack: &'h [u8],
    start: usize,
    end: usize,
}

impl<'h> Memchr2<'h> {
    pub fn new(needle1: u8, needle2: u8, haystack: &'h [u8]) -> Memchr2<'h> {
        Memchr2 { needle1, needle2, haystack, start: 0, end: haystack.len() }
    }
}

impl<'h> Iterator for Memchr2<'h> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        let i = memchr3_in(self.needle1, self.needle2, self.needle2, self.haystack, self.start, self.end)?;
        self.start = i + 1;
        Some(i)
    }

}


/// Every index of any of three needle bytes. See `Memchr`.
#[derive(Clone)]
pub struct Memchr3<'h> {
    needle1: u8,
    needle2: u8,
    needle3: u8,
    haystack: &'h [u8],
    start: usize,
    end: usize,
}

impl<'h> Memchr3<'h> {
    pub fn new(needle1: u8, needle2: u8, needle3: u8, haystack: &'h [u8]) -> Memchr3<'h> {
        Memchr3 { needle1, needle2, needle3, haystack, start: 0, end: haystack.len() }
    }
}

impl<'h> Iterator for Memchr3<'h> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        let i = memchr3_in(self.needle1, self.needle2, self.needle3, self.haystack, self.start, self.end)?;
        self.start = i + 1;
        Some(i)
    }

}

