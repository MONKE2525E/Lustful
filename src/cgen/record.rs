// B1 (rel-front, docs: B1-DESIGN.md): what a release C fn unit's text is made of. While the
// driver holds a record open on this thread (`open`, `close`), each emission site of
// `fn_unit_parts` and `type_decls_with` hands the exact text it appended, as a piece with
// its kind and the item it came from. `close` keeps the record only when the pieces make the
// whole unit text, byte for byte: text emitted outside a recorded site makes the unit
// unrecorded (fail closed), never a wrong record. Recording reads the text after it is
// written, so a unit's text is the same with or without a record. Off unless open: dev
// builds, the daemon and LLVM-backend units (`abandon`) never record.
use std::cell::RefCell;

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

thread_local! {
    /// The open record: its pieces and their text so far.
    static OPEN: RefCell<Option<(Vec<Piece>, String)>> = const { RefCell::new(None) };
}

/// Starts recording the next unit this thread assembles.
pub fn open() {
    OPEN.with(|r| *r.borrow_mut() = Some((Vec::new(), String::new())));
}

/// True while a record is open on this thread.
pub fn on() -> bool {
    OPEN.with(|r| r.borrow().is_some())
}

/// Records `text` (just appended to the unit) as its next piece; nothing without a record.
pub fn piece(kind: Kind, key: u64, text: &str) {
    OPEN.with(|r| {
        if let Some((pieces, all)) = r.borrow_mut().as_mut() {
            pieces.push(Piece { kind, key, hash: crate::driver::cache::hash128(&[text.as_bytes()], 0), len: text.len() });
            all.push_str(text);
        }
    });
}

/// Drops the open record: this unit is never memoized (an LLVM-backend unit).
pub fn abandon() {
    OPEN.with(|r| *r.borrow_mut() = None);
}

/// Ends the record: its pieces when they make exactly `whole`, else none.
pub fn close(whole: &str) -> Option<Vec<Piece>> {
    let open = OPEN.with(|r| r.borrow_mut().take());
    open.and_then(|(pieces, all)| (all == whole).then_some(pieces))
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
        assert_eq!(close(whole).map(|p| p.len()), Some(2));
        open();
        piece(Kind::Fixed, 0, "head\n");
        assert_eq!(close(whole), None, "text outside the pieces");
        piece(Kind::Fixed, 0, "nothing open");
        assert!(!on() && close("nothing open").is_none(), "no record without open");
    }
}
