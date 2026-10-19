// B1 (rel-front, docs: B1-DESIGN.md): what a release C fn unit's text is made of. While the
// driver holds a record open on this thread (`open`, `close`), each emission site of
// `fn_unit_parts` and `type_decls_with` hands the exact text it appended, as a piece with
// its kind and the item it came from. `close` keeps the record only when the pieces make the
// whole unit text, byte for byte: text emitted outside a recorded site makes the unit
// unrecorded (fail closed), never a wrong record. Recording reads the text after it is
// written, so a unit's text is the same with or without a record. Off unless open: dev
// builds, the daemon and LLVM-backend units (`abandon`) never record.
use std::cell::RefCell;
use std::collections::HashSet;

/// What a piece of a unit is.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Kind {
    /// Text the unit always has: its header, the noreturn prototypes, the hash core.
    Fixed,
    /// One type's forward typedefs and definition (`type_decls_with`).
    TypeDecl,
    /// The extern statics the code names.
    Statics,
    /// The extern prototypes the code and its glue name.
    Externs,
    /// An inline copy of a small callee: its prototype lines or its definition.
    InlineDef,
    /// A glue prototype (with its `static` or `inline` mark).
    GlueProto,
    /// An inline or static glue definition.
    GlueDef,
    /// One of the unit's own fn bodies.
    Body,
    /// The termination entry of a `main` returning `ExitCode` or `Result`.
    Entry,
    /// The registration function.
    Register,
}

/// One recorded piece: its kind, its item (a hash of the item's identity), and a hash and
/// length of its text.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Piece {
    pub kind: Kind,
    pub key: u64,
    pub hash: (u64, u64),
    pub len: usize,
}

/// What a unit read to choose and make its pieces (B1 step 2): the next build compares each
/// read's fingerprint (`cgen::read_fp`), so a unit whose reads all stand is made of the
/// same text without being assembled.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Read {
    /// A fn's output (`FnOut`) and release name, by slot.
    Fn(usize),
    /// The slot a fn id names (`names::slot_of_id`).
    SlotOf(String),
    /// A callee `inline_callees` left out (by slot, and whether at a deep level): only that
    /// it is still left out (`inline_pick`), not its whole output.
    Pick(usize, bool),
    /// A glue key's entry in the glue set.
    Glue(super::Glue, super::CTy),
    /// What a type's declarations print and the types they reach, with the type's release
    /// name when it was read (an Adt id can name another Adt in a later build).
    Type(super::CTy, String),
    /// The static a `lust_static_*` symbol of the unit's text names, by symbol.
    Static(String),
    /// The main fn and its return type.
    Main,
}

/// What the last build recorded of one unit (the driver's `Caches::unit_records`): its
/// identity (registration name, fns, switches), its pieces, each read with the fingerprint it
/// had (`cgen::read_fp`), and the unit's fingerprint over both (`new`), the key the unit memo
/// (`cc::UnitIn::fp`) knows its object by.
#[derive(Clone, Debug)]
pub struct UnitRecord {
    pub id: (u64, u64),
    pub pieces: Vec<Piece>,
    pub reads: Vec<(Read, (u64, u64))>,
    pub fp: u128,
}

impl UnitRecord {
    /// The record of a unit just assembled. Its fingerprint takes no read order (a record
    /// keeps its reads as they came): the identity's hash with the sum of one hash per read
    /// and its fingerprint, so the same identity and reads give the same fingerprint in any
    /// build. Units differ in identity (their registration names), so two units never share one.
    pub fn new(id: (u64, u64), pieces: Vec<Piece>, reads: Vec<(Read, (u64, u64))>) -> UnitRecord {
        use std::hash::{Hash, Hasher};
        let sum = reads.iter().fold(0u128, |sum, (r, f)| {
            let mut h = crate::intern::FxHasher::default();
            r.hash(&mut h);
            let (a, b) = crate::driver::cache::hash128(&[&h.finish().to_le_bytes(), &f.0.to_le_bytes(), &f.1.to_le_bytes()], 15);
            sum.wrapping_add((a as u128) << 64 | b as u128)
        });
        let (a, b) = crate::driver::cache::hash128(&[&id.0.to_le_bytes(), &id.1.to_le_bytes(), &sum.to_le_bytes()], 14);
        UnitRecord { id, pieces, reads, fp: (a as u128) << 64 | b as u128 }
    }
}

/// The open record: its pieces, their text so far, and its reads.
type Open = (Vec<Piece>, String, HashSet<Read>);

thread_local! {
    static OPEN: RefCell<Option<Open>> = const { RefCell::new(None) };
}

/// Starts recording the next unit this thread assembles.
pub fn open() {
    OPEN.with(|r| *r.borrow_mut() = Some((Vec::new(), String::new(), HashSet::new())));
}

/// Records a read of the open unit; nothing without a record.
pub fn read(what: Read) {
    OPEN.with(|r| {
        if let Some((_, _, reads)) = r.borrow_mut().as_mut() {
            reads.insert(what);
        }
    });
}

/// True while a record is open on this thread.
pub fn on() -> bool {
    OPEN.with(|r| r.borrow().is_some())
}

/// Records `text` (just appended to the unit) as its next piece; nothing without a record.
pub fn piece(kind: Kind, key: u64, text: &str) {
    OPEN.with(|r| {
        if let Some((pieces, all, _)) = r.borrow_mut().as_mut() {
            pieces.push(Piece { kind, key, hash: crate::driver::cache::hash128(&[text.as_bytes()], 0), len: text.len() });
            all.push_str(text);
        }
    });
}

/// Drops the open record: this unit is never memoized (an LLVM-backend unit).
pub fn abandon() {
    OPEN.with(|r| *r.borrow_mut() = None);
}

/// Ends the record: its pieces and reads when the pieces make exactly `whole`, else none.
pub fn close(whole: &str) -> Option<(Vec<Piece>, Vec<Read>)> {
    let open = OPEN.with(|r| r.borrow_mut().take());
    open.and_then(|(pieces, all, reads)| (all == whole).then(|| (pieces, reads.into_iter().collect())))
}

/// A key for an item given by name or text (a type's mangled name, a fn's tag).
pub fn key(name: &str) -> u64 {
    crate::driver::cache::hash128(&[name.as_bytes()], 1).0
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A record holds when its pieces make the whole text, and fails closed when a byte of
    /// the text came from no piece.
    #[test]
    fn a_record_fails_closed() {
        open();
        piece(Kind::Fixed, 0, "head\n");
        piece(Kind::Body, key("f"), "int f(void) { return 1; }\n");
        let whole = "head\nint f(void) { return 1; }\n";
        assert_eq!(close(whole).map(|(p, _)| p.len()), Some(2));
        open();
        piece(Kind::Fixed, 0, "head\n");
        assert_eq!(close(whole), None, "text outside the pieces");
        piece(Kind::Fixed, 0, "nothing open");
        assert!(!on() && close("nothing open").is_none(), "no record without open");
    }

    /// A unit's fingerprint follows its identity and its reads' fingerprints, not the order
    /// the reads came in.
    #[test]
    fn the_unit_fingerprint_is_its_reads() {
        let reads = vec![(Read::Fn(3), (1, 2)), (Read::Static("lust_static_a".into()), (3, 4)), (Read::Main, (5, 6))];
        let mut turned = reads.clone();
        turned.reverse();
        let a = UnitRecord::new((7, 8), Vec::new(), reads.clone());
        assert_eq!(a.fp, UnitRecord::new((7, 8), Vec::new(), turned).fp);
        let mut moved = reads.clone();
        moved[1].1 = (3, 5);
        assert_ne!(a.fp, UnitRecord::new((7, 8), Vec::new(), moved).fp, "a read whose fingerprint moved");
        assert_ne!(a.fp, UnitRecord::new((7, 9), Vec::new(), reads).fp, "another identity");
    }
}
