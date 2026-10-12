#!/usr/bin/env python3
"""Turn rustc -Zunpretty=expanded output into a token sequence.

Usage: normalize.py < expanded.rs > case.expanded

ARCH 6.5: the printed expansion is lossy, so the corpus compares
tokens, not text. This tokenizer drops comments and all whitespace
structure and writes the token stream space-joined and wrapped. It is a lexer for the
already-valid output of the pretty printer, not a Rust lexer: it
only needs to split that output the same way every time.
"""
import sys

MULTI = ["..=", "...", "=>", "->", "::", "..", "<<", ">>", "&&", "||",
         "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "==", "!=",
         "<=", ">=", ">>=", "<<="]


def tokens(text):
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
            continue
        if text.startswith("//", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if text.startswith("/*", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if text.startswith("/*", i):
                    depth += 1
                    i += 2
                elif text.startswith("*/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            continue
        # Raw string r##"..."## and raw identifier r#name. A plain
        # identifier that starts with r falls through to ident below.
        if c == "r" and i + 1 < n and (text[i + 1] == "#" or text[i + 1] == '"'):
            j = i + 1
            while j < n and text[j] == "#":
                j += 1
            if j < n and text[j] == '"':
                hashes = j - i - 1
                end = '"' + "#" * hashes
                k = text.find(end, j + 1)
                k = n if k < 0 else k + len(end)
                yield text[i:k]
                i = k
                continue
            # raw identifier: r# plus an ident that is not a quote
            if j == i + 2 and j < n and (text[j].isalpha() or text[j] == "_"):
                k = j
                while k < n and (text[k].isalnum() or text[k] == "_"):
                    k += 1
                yield text[i:k]
                i = k
                continue
        # String, byte string, char, byte char, lifetime.
        if c == '"' or (c == "b" and i + 1 < n and text[i + 1] in "\"'"):
            j = i + 1 if c == '"' else i + 2
            quote = '"' if c == '"' or text[i + 1] == '"' else "'"
            while j < n:
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == quote:
                    j += 1
                    break
                j += 1
            yield text[i:j]
            i = j
            continue
        if c == "'":
            # Char literal ('x', '\n', '\'' ...) vs lifetime ('a, 'static).
            if i + 2 < n and text[i + 2] == "'":
                yield text[i:i + 3]
                i += 3
                continue
            if i + 1 < n and text[i + 1] == "\\":
                j = text.find("'", i + 2)
                j = n if j < 0 else j + 1
                yield text[i:j]
                i = j
                continue
            j = i + 1
            while j < n and (text[j].isalnum() or text[j] == "_"):
                j += 1
            yield text[i:j]
            i = j
            continue
        if c.isalpha() or c == "_":
            j = i
            while j < n and (text[j].isalnum() or text[j] == "_"):
                j += 1
            yield text[i:j]
            i = j
            continue
        if c.isdigit():
            j = i
            while j < n and (text[j].isalnum() or text[j] in "_-."):
                # Do not eat a range or a field access after the number.
                if text[j] == "." and j + 1 < n and not text[j + 1].isdigit():
                    break
                if text[j] == "-" and not (j > i and text[j - 1] in "eE"):
                    break
                j += 1
            yield text[i:j]
            i = j
            continue
        matched = False
        for m in MULTI:
            if text.startswith(m, i):
                yield m
                i += len(m)
                matched = True
                break
        if not matched:
            yield c
            i += 1


def main():
    # Space-joined tokens, wrapped at 100 columns. Wrapping is
    # cosmetic: normalize.py on its own output gives the same text.
    out = sys.stdout
    col = 0
    for tok in tokens(sys.stdin.read()):
        if col and col + 1 + len(tok) > 100:
            out.write("\n")
            col = 0
        if col:
            out.write(" ")
            col += 1
        out.write(tok)
        col += len(tok)
    if col:
        out.write("\n")


if __name__ == "__main__":
    main()
