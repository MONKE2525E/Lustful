//! Go `strconv.Quote` and its helpers (go1.27.1 `src/strconv/quote.go` and
//! `src/strconv/isprint.go`, Unicode 17.0.0, the toolchain of the pin N
//! oracle). Go `%q` of a string is `quote(s)`.
//!
//! The `IsPrint` tables are generated from Go's `isprint.go`
//! (`strconv_isprint.rs`, `scripts/goport/gen/unicode/gen.sh`), so the
//! result equals Go's for every rune.
//!
//! PORT: Go strings may hold invalid UTF-8, which `Quote` writes as `\x..`.
//! A port string holds such bytes (and lone surrogates) in the port form
//! (`scanner_util::GO_STRING_MARKER`). The quote functions quote a string
//! with marker units from its Go bytes, as Go does (`quote_bytes`).

use crate::prelude::*;


const LOWERHEX: &[u8; 16] = b"0123456789abcdef";

/// Go `utf8.RuneSelf`.
const RUNE_SELF: u32 = 0x80;

// Go: strconv/quote.go:23 quoteWith
// PORT: `s` is a Go string in the port form. One with marker units is
// quoted from its Go bytes, so a raw byte is `\x..` as in Go (not the
// escapes of the marker chars).


// Go: strconv/quote.go:23 quoteWith, on Go bytes.

// Go: strconv/quote.go:27 quoteRuneWith

// Go: strconv/quote.go:31 appendQuotedWith

// Go: strconv/quote.go:54 appendQuotedRuneWith
// PORT: a Rust `char` is always a valid rune, so Go's `utf8.ValidRune` check
// is always true.

// Go: strconv/quote.go:64 appendEscapedRune

// Go: strconv/quote.go:121 Quote

// Go: strconv/quote.go:134 QuoteToASCII

// Go: strconv/quote.go:148 QuoteToGraphic

// Go: strconv/quote.go:163 QuoteRune

// Go: strconv/quote.go:179 QuoteRuneToASCII

// Go: strconv/quote.go:195 QuoteRuneToGraphic

// Go: strconv/quote.go:495 bsearch
/// bsearch is semantically the same as [slices.BinarySearch] (without NaN checks)
/// We copied this function because we can not import "slices" here.
fn bsearch<E: Ord + Copy>(s: &[E], v: E) -> (usize, bool) {
    let n = s.len();
    let (mut i, mut j) = (0usize, n);
    while i < j {
        let h = i + (j - i) / 2;
        if s[h] < v {
            i = h + 1;
        } else {
            j = h;
        }
    }
    (i, i < n && s[i] == v)
}

// Go: strconv/quote.go:518 IsPrint

// Go: strconv/quote.go:564 IsGraphic

// Go: strconv/quote.go:574 isInGraphicList

#[cfg(test)]
mod tests {
    use super::*;

    // go1.27.1 (Unicode 17.0.0): the count and the sum of the runes with
    // IsPrint (IsGraphic) true. go1.26.8 (Unicode 15.0.0) gave 148998 and
    // 15_750_900_724 (149014 and 15_751_025_625).
    #[test]
    fn is_print_uses_unicode_17() {
        let chars = || (0..=0x10FFFF).filter_map(char::from_u32);
        let count = |f: fn(char) -> bool| {
            let hits = || chars().filter(|&c| f(c));
            (hits().count(), hits().map(u64::from).sum::<u64>())
        };
        assert_eq!(count(is_print), (159_613, 17_258_563_829));
        assert_eq!(count(is_graphic), (159_629, 17_258_688_730));
    }

    // go1.27.1 strconv.Quote writes the Unicode 16.0 and 17.0 letters as they
    // are; go1.26.8 wrote "\ua7cb", "\U00010d50" and "\U00016ea0".
    #[test]
    fn quote_keeps_unicode_17_letters() {
        assert_eq!(quote("\u{A7CB}"), "\"\u{A7CB}\"");
        assert_eq!(quote("\u{10D50}"), "\"\u{10D50}\"");
        assert_eq!(quote("\u{16EA0}"), "\"\u{16EA0}\"");
        assert_eq!(quote("a\u{378}b"), "\"a\\u0378b\"");
    }

    // Go `%q` of a string with raw bytes writes each byte that is not
    // valid UTF-8 as `\x..` (strconv/quote.go:42). The port form holds
    // such bytes as marker units (`go_string_from_bytes`, as an OS argument
    // gets them), and a real U+FDD0 as two markers. Texts from Go N:
    // `--lsp -clientProcessId=$'\xff\xfe'` gives `invalid value "\xff\xfe"`
    // (followups24 skeptic).
    #[test]
    fn quote_writes_the_go_bytes_of_marker_units() {
        use crate::scanner_util::go_string_from_bytes;
        let quoted = |bytes: &[u8]| quote(&go_string_from_bytes(bytes.to_vec()));
        assert_eq!(quoted(b"\xff\xfe"), r#""\xff\xfe""#);
        assert_eq!(quoted(b"a\xffb\n"), r#""a\xffb\n""#);
        assert_eq!(
            quoted(&["\u{FDD0}xé".as_bytes(), b"\xff".as_slice()].concat()),
            "\"\\ufdd0xé\\xff\""
        );
        // A WTF-8 lone surrogate is three invalid bytes in Go.
        assert_eq!(quoted(b"\xed\xa0\x80"), r#""\xed\xa0\x80""#);
        assert_eq!(
            quote_bytes(b"\xe2\x82A\xf0\x9f\x98\x80"),
            "\"\\xe2\\x82A\u{1F600}\""
        );
        assert_eq!(
            quote_to_ascii(&go_string_from_bytes(
                [b"\xff".as_slice(), "é".as_bytes()].concat()
            )),
            r#""\xff\u00e9""#
        );
    }
}
