// Error spellings and positions follow serde_json 1.0.151 (MIT).
use std::fmt;

pub struct Error {
    code: ErrorCode,
    line: usize,
    column: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Category { Io, Syntax, Data, Eof }

#[derive(Clone, Copy)]
pub(crate) enum ErrorCode {
    EofWhileParsingList,
    EofWhileParsingObject,
    EofWhileParsingString,
    EofWhileParsingValue,
    ExpectedColon,
    ExpectedListCommaOrEnd,
    ExpectedObjectCommaOrEnd,
    ExpectedSomeIdent,
    ExpectedSomeValue,
    InvalidEscape,
    InvalidNumber,
    NumberOutOfRange,
    InvalidUnicodeCodePoint,
    ControlCharacterWhileParsingString,
    KeyMustBeAString,
    LoneLeadingSurrogateInHexEscape,
    TrailingComma,
    TrailingCharacters,
    UnexpectedEndOfHexEscape,
    RecursionLimitExceeded,
}

impl Error {
    pub(crate) fn new(code: ErrorCode, line: usize, column: usize) -> Self {
        Self { code, line, column }
    }
    pub fn line(&self) -> usize { self.line }
    pub fn column(&self) -> usize { self.column }
    pub fn classify(&self) -> Category {
        match self.code {
            ErrorCode::EofWhileParsingList | ErrorCode::EofWhileParsingObject |
            ErrorCode::EofWhileParsingString | ErrorCode::EofWhileParsingValue => Category::Eof,
            _ => Category::Syntax,
        }
    }
    pub fn is_io(&self) -> bool { self.classify() == Category::Io }
    pub fn is_data(&self) -> bool { self.classify() == Category::Data }
    pub fn is_syntax(&self) -> bool { self.classify() == Category::Syntax }
    pub fn is_eof(&self) -> bool { self.classify() == Category::Eof }
}

impl fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::EofWhileParsingList => "EOF while parsing a list",
            Self::EofWhileParsingObject => "EOF while parsing an object",
            Self::EofWhileParsingString => "EOF while parsing a string",
            Self::EofWhileParsingValue => "EOF while parsing a value",
            Self::ExpectedColon => "expected `:`",
            Self::ExpectedListCommaOrEnd => "expected `,` or `]`",
            Self::ExpectedObjectCommaOrEnd => "expected `,` or `}`",
            Self::ExpectedSomeIdent => "expected ident",
            Self::ExpectedSomeValue => "expected value",
            Self::InvalidEscape => "invalid escape",
            Self::InvalidNumber => "invalid number",
            Self::NumberOutOfRange => "number out of range",
            Self::InvalidUnicodeCodePoint => "invalid unicode code point",
            Self::ControlCharacterWhileParsingString =>
                "control character (\\u0000-\\u001F) found while parsing a string",
            Self::KeyMustBeAString => "key must be a string",
            Self::LoneLeadingSurrogateInHexEscape => "lone leading surrogate in hex escape",
            Self::TrailingComma => "trailing comma",
            Self::TrailingCharacters => "trailing characters",
            Self::UnexpectedEndOfHexEscape => "unexpected end of hex escape",
            Self::RecursionLimitExceeded => "recursion limit exceeded",
        })
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at line {} column {}", self.code, self.line, self.column)
    }
}
impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Error({:?}, line: {}, column: {})", self.code.to_string(), self.line, self.column)
    }
}
impl std::error::Error for Error {}
