// Owned Value parsing adapted from serde_json 1.0.151 de.rs and read.rs.
// MIT license: ../LICENSE-MIT. No Serde visitor or borrowed-output API.
use crate::error::ErrorCode;
use crate::{Error, Map, Number, Result, Value};

mod sealed {
    pub trait Sealed {}
}

/// Closed owned decode bound; this is not serde::Deserialize.
#[doc(hidden)]
pub trait OwnedJsonDecode: sealed::Sealed {
    #[doc(hidden)]
    fn __from_json_slice(input: &[u8]) -> Result<Self> where Self: Sized;
}

impl sealed::Sealed for Value {}
impl OwnedJsonDecode for Value {
    fn __from_json_slice(input: &[u8]) -> Result<Self> { parse(input) }
}

pub fn from_str<T: OwnedJsonDecode>(input: &str) -> Result<T> {
    T::__from_json_slice(input.as_bytes())
}

pub fn from_slice<T: OwnedJsonDecode>(input: &[u8]) -> Result<T> {
    T::__from_json_slice(input)
}

fn parse(input: &[u8]) -> Result<Value> {
    let mut parser = Parser { input, index: 0, remaining_depth: 128 };
    let value = parser.value()?;
    if parser.whitespace().is_some() {
        return Err(parser.peek_error(ErrorCode::TrailingCharacters));
    }
    Ok(value)
}

struct Parser<'a> {
    input: &'a [u8],
    index: usize,
    remaining_depth: u8,
}

// The numeric methods below retain upstream's fallible-read spelling.
macro_rules! tri {
    ($expr:expr $(,)?) => { $expr? };
}
macro_rules! overflow {
    ($a:ident * 10 + $b:ident, $c:expr) => {
        match $c {
            c => $a >= c / 10 && ($a > c / 10 || $b > c % 10),
        }
    };
}

enum ParserNumber {
    U64(u64),
    I64(i64),
    F64(f64),
}

impl<'a> Parser<'a> {
    fn peek_byte(&self) -> Option<u8> { self.input.get(self.index).copied() }
    fn peek(&self) -> Result<Option<u8>> { Ok(self.peek_byte()) }
    fn peek_or_null(&self) -> Result<u8> { Ok(self.peek_byte().unwrap_or(0)) }
    fn eat_char(&mut self) { self.index += 1; }
    fn next_char(&mut self) -> Result<Option<u8>> {
        let ch = self.peek_byte();
        if ch.is_some() { self.index += 1; }
        Ok(ch)
    }

    fn error_at(&self, code: ErrorCode, index: usize) -> Error {
        let mut line = 1;
        let mut column = 0;
        for byte in &self.input[..index] {
            if *byte == b'\n' { line += 1; column = 0; }
            else { column += 1; }
        }
        Error::new(code, line, column)
    }
    fn error(&self, code: ErrorCode) -> Error { self.error_at(code, self.index) }
    fn peek_error(&self, code: ErrorCode) -> Error {
        let index = if self.index < self.input.len() { self.index + 1 } else { self.index };
        self.error_at(code, index)
    }
    fn whitespace(&mut self) -> Option<u8> {
        loop {
            match self.peek_byte() {
                Some(b' ' | b'\n' | b'\r' | b'\t') => self.eat_char(),
                ch => return ch,
            }
        }
    }
    fn ident(&mut self, rest: &[u8]) -> Result<()> {
        for expected in rest {
            match self.next_char()? {
                Some(ch) if ch == *expected => {}
                Some(_) => return Err(self.error(ErrorCode::ExpectedSomeIdent)),
                None => return Err(self.error(ErrorCode::EofWhileParsingValue)),
            }
        }
        Ok(())
    }
    fn value(&mut self) -> Result<Value> {
        match self.whitespace() {
            Some(b'n') => { self.eat_char(); self.ident(b"ull")?; Ok(Value::Null) }
            Some(b't') => { self.eat_char(); self.ident(b"rue")?; Ok(Value::Bool(true)) }
            Some(b'f') => { self.eat_char(); self.ident(b"alse")?; Ok(Value::Bool(false)) }
            Some(b'"') => { self.eat_char(); Ok(Value::String(self.string()?)) }
            Some(b'-') => { self.eat_char(); self.number(false) }
            Some(b'0'..=b'9') => self.number(true),
            Some(b'[' | b'{') => {
                // Upstream checks before consuming the opening delimiter.
                self.remaining_depth -= 1;
                if self.remaining_depth == 0 {
                    return Err(self.peek_error(ErrorCode::RecursionLimitExceeded));
                }
                let opening = self.next_char()?;
                let result = if opening == Some(b'[') { self.array() } else { self.object() };
                self.remaining_depth += 1;
                result
            }
            Some(_) => Err(self.peek_error(ErrorCode::ExpectedSomeValue)),
            None => Err(self.peek_error(ErrorCode::EofWhileParsingValue)),
        }
    }
    fn number(&mut self, positive: bool) -> Result<Value> {
        let number = match self.parse_integer(positive)? {
            ParserNumber::U64(n) => Number::from(n),
            ParserNumber::I64(n) => Number::from(n),
            ParserNumber::F64(n) => Number::parsed_float(n),
        };
        Ok(Value::Number(number))
    }
    fn array(&mut self) -> Result<Value> {
        let mut out = Vec::new();
        let mut first = true;
        loop {
            match self.whitespace() {
                Some(b']') => { self.eat_char(); return Ok(Value::Array(out)); }
                None => return Err(self.peek_error(ErrorCode::EofWhileParsingList)),
                Some(_) if first => { first = false; }
                Some(b',') => {
                    self.eat_char();
                    match self.whitespace() {
                        Some(b']') => return Err(self.peek_error(ErrorCode::TrailingComma)),
                        None => return Err(self.peek_error(ErrorCode::EofWhileParsingValue)),
                        _ => {}
                    }
                }
                _ => return Err(self.peek_error(ErrorCode::ExpectedListCommaOrEnd)),
            }
            out.push(self.value()?);
        }
    }
    fn object(&mut self) -> Result<Value> {
        let mut out = Map::new();
        let mut first = true;
        loop {
            match self.whitespace() {
                Some(b'}') => { self.eat_char(); return Ok(Value::Object(out)); }
                None => return Err(self.peek_error(ErrorCode::EofWhileParsingObject)),
                Some(_) if first => { first = false; }
                Some(b',') => {
                    self.eat_char();
                    match self.whitespace() {
                        Some(b'}') => return Err(self.peek_error(ErrorCode::TrailingComma)),
                        None => return Err(self.peek_error(ErrorCode::EofWhileParsingValue)),
                        _ => {}
                    }
                }
                _ => return Err(self.peek_error(ErrorCode::ExpectedObjectCommaOrEnd)),
            }
            if self.peek_byte() != Some(b'"') {
                return Err(self.peek_error(ErrorCode::KeyMustBeAString));
            }
            self.eat_char();
            let key = self.string()?;
            match self.whitespace() {
                Some(b':') => self.eat_char(),
                Some(_) => return Err(self.peek_error(ErrorCode::ExpectedColon)),
                None => return Err(self.peek_error(ErrorCode::EofWhileParsingObject)),
            }
            let value = self.value()?;
            out.insert(key, value);
        }
    }
    fn string(&mut self) -> Result<String> {
        let mut bytes = Vec::new();
        loop {
            match self.next_char()? {
                Some(b'"') => return match String::from_utf8(bytes) {
                    Ok(s) => Ok(s),
                    Err(_) => Err(self.error(ErrorCode::InvalidUnicodeCodePoint)),
                },
                Some(b'\\') => self.escape(&mut bytes)?,
                Some(0..=0x1f) => return Err(self.error(ErrorCode::ControlCharacterWhileParsingString)),
                Some(ch) => bytes.push(ch),
                None => return Err(self.error(ErrorCode::EofWhileParsingString)),
            }
        }
    }
    fn string_byte(&mut self) -> Result<u8> {
        match self.next_char()? {
            Some(ch) => Ok(ch),
            None => Err(self.error(ErrorCode::EofWhileParsingString)),
        }
    }
    fn escape(&mut self, bytes: &mut Vec<u8>) -> Result<()> {
        match self.string_byte()? {
            b'"' => bytes.push(b'"'),
            b'\\' => bytes.push(b'\\'),
            b'/' => bytes.push(b'/'),
            b'b' => bytes.push(8),
            b'f' => bytes.push(12),
            b'n' => bytes.push(b'\n'),
            b'r' => bytes.push(b'\r'),
            b't' => bytes.push(b'\t'),
            b'u' => return self.unicode_escape(bytes),
            _ => return Err(self.error(ErrorCode::InvalidEscape)),
        }
        Ok(())
    }
    fn hex4(&mut self) -> Result<u16> {
        // SliceRead advances all four bytes before checking *any* hex digit.
        if self.input.len() - self.index < 4 {
            self.index = self.input.len();
            return Err(self.error(ErrorCode::EofWhileParsingString));
        }
        let start = self.index;
        self.index += 4;
        let mut n = 0;
        for byte in &self.input[start..self.index] {
            let digit = match *byte {
                b'0'..=b'9' => *byte - b'0',
                b'a'..=b'f' => *byte - b'a' + 10,
                b'A'..=b'F' => *byte - b'A' + 10,
                _ => return Err(self.error(ErrorCode::InvalidEscape)),
            };
            n = (n << 4) | digit as u16;
        }
        Ok(n)
    }
    fn unicode_escape(&mut self, bytes: &mut Vec<u8>) -> Result<()> {
        let first = self.hex4()?;
        if (0xdc00..=0xdfff).contains(&first) {
            return Err(self.error(ErrorCode::LoneLeadingSurrogateInHexEscape));
        }
        let scalar = if (0xd800..=0xdbff).contains(&first) {
            if self.string_byte()? != b'\\' {
                return Err(self.error(ErrorCode::UnexpectedEndOfHexEscape));
            }
            if self.string_byte()? != b'u' {
                return Err(self.error(ErrorCode::UnexpectedEndOfHexEscape));
            }
            let second = self.hex4()?;
            if !(0xdc00..=0xdfff).contains(&second) {
                return Err(self.error(ErrorCode::LoneLeadingSurrogateInHexEscape));
            }
            (((first - 0xd800) as u32) << 10 | (second - 0xdc00) as u32) + 0x10000
        } else { first as u32 };
        // Only scalar values reach here. Safe explicit UTF-8 avoids unchecked
        // conversion and does not require a new Unicode-construction intrinsic.
        if scalar < 0x80 { bytes.push(scalar as u8); }
        else if scalar < 0x800 {
            bytes.push((scalar >> 6) as u8 | 0xc0);
            bytes.push((scalar & 0x3f) as u8 | 0x80);
        } else if scalar < 0x10000 {
            bytes.push((scalar >> 12) as u8 | 0xe0);
            bytes.push(((scalar >> 6) & 0x3f) as u8 | 0x80);
            bytes.push((scalar & 0x3f) as u8 | 0x80);
        } else {
            bytes.push((scalar >> 18) as u8 | 0xf0);
            bytes.push(((scalar >> 12) & 0x3f) as u8 | 0x80);
            bytes.push(((scalar >> 6) & 0x3f) as u8 | 0x80);
            bytes.push((scalar & 0x3f) as u8 | 0x80);
        }
        Ok(())
    }
    fn parse_integer(&mut self, positive: bool) -> Result<ParserNumber> {
        let next = match tri!(self.next_char()) {
            Some(b) => b,
            None => {
                return Err(self.error(ErrorCode::EofWhileParsingValue));
            }
        };

        match next {
            b'0' => {
                // There can be only one leading '0'.
                match tri!(self.peek_or_null()) {
                    b'0'..=b'9' => Err(self.peek_error(ErrorCode::InvalidNumber)),
                    _ => self.parse_number(positive, 0),
                }
            }
            c @ b'1'..=b'9' => {
                let mut significand = (c - b'0') as u64;

                loop {
                    match tri!(self.peek_or_null()) {
                        c @ b'0'..=b'9' => {
                            let digit = (c - b'0') as u64;

                            // We need to be careful with overflow. If we can,
                            // try to keep the number as a `u64` until we grow
                            // too large. At that point, switch to parsing the
                            // value as a `f64`.
                            if overflow!(significand * 10 + digit, u64::MAX) {
                                return Ok(ParserNumber::F64(tri!(
                                    self.parse_long_integer(positive, significand),
                                )));
                            }

                            self.eat_char();
                            significand = significand * 10 + digit;
                        }
                        _ => {
                            return self.parse_number(positive, significand);
                        }
                    }
                }
            }
            _ => Err(self.error(ErrorCode::InvalidNumber)),
        }
    }

    fn parse_number(&mut self, positive: bool, significand: u64) -> Result<ParserNumber> {
        Ok(match tri!(self.peek_or_null()) {
            b'.' => ParserNumber::F64(tri!(self.parse_decimal(positive, significand, 0))),
            b'e' | b'E' => ParserNumber::F64(tri!(self.parse_exponent(positive, significand, 0))),
            _ => {
                if positive {
                    ParserNumber::U64(significand)
                } else {
                    let neg = (significand as i64).wrapping_neg();

                    // Convert into a float if we underflow, or on `-0`.
                    if neg >= 0 {
                        ParserNumber::F64(-(significand as f64))
                    } else {
                        ParserNumber::I64(neg)
                    }
                }
            }
        })
    }

    fn parse_decimal(
        &mut self,
        positive: bool,
        mut significand: u64,
        exponent_before_decimal_point: i32,
    ) -> Result<f64> {
        self.eat_char();

        let mut exponent_after_decimal_point = 0;
        while let c @ b'0'..=b'9' = tri!(self.peek_or_null()) {
            let digit = (c - b'0') as u64;

            if overflow!(significand * 10 + digit, u64::MAX) {
                let exponent = exponent_before_decimal_point + exponent_after_decimal_point;
                return self.parse_decimal_overflow(positive, significand, exponent);
            }

            self.eat_char();
            significand = significand * 10 + digit;
            exponent_after_decimal_point -= 1;
        }

        // Error if there is not at least one digit after the decimal point.
        if exponent_after_decimal_point == 0 {
            match tri!(self.peek()) {
                Some(_) => return Err(self.peek_error(ErrorCode::InvalidNumber)),
                None => return Err(self.peek_error(ErrorCode::EofWhileParsingValue)),
            }
        }

        let exponent = exponent_before_decimal_point + exponent_after_decimal_point;
        match tri!(self.peek_or_null()) {
            b'e' | b'E' => self.parse_exponent(positive, significand, exponent),
            _ => self.f64_from_parts(positive, significand, exponent),
        }
    }

    fn parse_exponent(
        &mut self,
        positive: bool,
        significand: u64,
        starting_exp: i32,
    ) -> Result<f64> {
        self.eat_char();

        let positive_exp = match tri!(self.peek_or_null()) {
            b'+' => {
                self.eat_char();
                true
            }
            b'-' => {
                self.eat_char();
                false
            }
            _ => true,
        };

        let next = match tri!(self.next_char()) {
            Some(b) => b,
            None => {
                return Err(self.error(ErrorCode::EofWhileParsingValue));
            }
        };

        // Make sure a digit follows the exponent place.
        let mut exp = match next {
            c @ b'0'..=b'9' => (c - b'0') as i32,
            _ => {
                return Err(self.error(ErrorCode::InvalidNumber));
            }
        };

        while let c @ b'0'..=b'9' = tri!(self.peek_or_null()) {
            self.eat_char();
            let digit = (c - b'0') as i32;

            if overflow!(exp * 10 + digit, i32::MAX) {
                let zero_significand = significand == 0;
                return self.parse_exponent_overflow(positive, zero_significand, positive_exp);
            }

            exp = exp * 10 + digit;
        }

        let final_exp = if positive_exp {
            starting_exp.saturating_add(exp)
        } else {
            starting_exp.saturating_sub(exp)
        };

        self.f64_from_parts(positive, significand, final_exp)
    }

    fn f64_from_parts(
        &mut self,
        positive: bool,
        significand: u64,
        mut exponent: i32,
    ) -> Result<f64> {
        let mut f = significand as f64;
        loop {
            match POW10.get(exponent.wrapping_abs() as usize) {
                Some(&pow) => {
                    if exponent >= 0 {
                        f *= pow;
                        if f.is_infinite() {
                            return Err(self.error(ErrorCode::NumberOutOfRange));
                        }
                    } else {
                        f /= pow;
                    }
                    break;
                }
                None => {
                    if f == 0.0 {
                        break;
                    }
                    if exponent >= 0 {
                        return Err(self.error(ErrorCode::NumberOutOfRange));
                    }
                    f /= 1e308;
                    exponent += 308;
                }
            }
        }
        Ok(if positive { f } else { -f })
    }

    fn parse_long_integer(&mut self, positive: bool, significand: u64) -> Result<f64> {
        let mut exponent = 0;
        loop {
            match tri!(self.peek_or_null()) {
                b'0'..=b'9' => {
                    self.eat_char();
                    // This could overflow... if your integer is gigabytes long.
                    // Ignore that possibility.
                    exponent += 1;
                }
                b'.' => {
                    return self.parse_decimal(positive, significand, exponent);
                }
                b'e' | b'E' => {
                    return self.parse_exponent(positive, significand, exponent);
                }
                _ => {
                    return self.f64_from_parts(positive, significand, exponent);
                }
            }
        }
    }

    fn parse_decimal_overflow(
        &mut self,
        positive: bool,
        significand: u64,
        exponent: i32,
    ) -> Result<f64> {
        // The next multiply/add would overflow, so just ignore all further
        // digits.
        while let b'0'..=b'9' = tri!(self.peek_or_null()) {
            self.eat_char();
        }

        match tri!(self.peek_or_null()) {
            b'e' | b'E' => self.parse_exponent(positive, significand, exponent),
            _ => self.f64_from_parts(positive, significand, exponent),
        }
    }

    fn parse_exponent_overflow(
        &mut self,
        positive: bool,
        zero_significand: bool,
        positive_exp: bool,
    ) -> Result<f64> {
        // Error instead of +/- infinity.
        if !zero_significand && positive_exp {
            return Err(self.error(ErrorCode::NumberOutOfRange));
        }

        while let b'0'..=b'9' = tri!(self.peek_or_null()) {
            self.eat_char();
        }
        Ok(if positive { 0.0 } else { -0.0 })
    }

}

static POW10: [f64; 309] = [
    1e000, 1e001, 1e002, 1e003, 1e004, 1e005, 1e006, 1e007, 1e008, 1e009, //
    1e010, 1e011, 1e012, 1e013, 1e014, 1e015, 1e016, 1e017, 1e018, 1e019, //
    1e020, 1e021, 1e022, 1e023, 1e024, 1e025, 1e026, 1e027, 1e028, 1e029, //
    1e030, 1e031, 1e032, 1e033, 1e034, 1e035, 1e036, 1e037, 1e038, 1e039, //
    1e040, 1e041, 1e042, 1e043, 1e044, 1e045, 1e046, 1e047, 1e048, 1e049, //
    1e050, 1e051, 1e052, 1e053, 1e054, 1e055, 1e056, 1e057, 1e058, 1e059, //
    1e060, 1e061, 1e062, 1e063, 1e064, 1e065, 1e066, 1e067, 1e068, 1e069, //
    1e070, 1e071, 1e072, 1e073, 1e074, 1e075, 1e076, 1e077, 1e078, 1e079, //
    1e080, 1e081, 1e082, 1e083, 1e084, 1e085, 1e086, 1e087, 1e088, 1e089, //
    1e090, 1e091, 1e092, 1e093, 1e094, 1e095, 1e096, 1e097, 1e098, 1e099, //
    1e100, 1e101, 1e102, 1e103, 1e104, 1e105, 1e106, 1e107, 1e108, 1e109, //
    1e110, 1e111, 1e112, 1e113, 1e114, 1e115, 1e116, 1e117, 1e118, 1e119, //
    1e120, 1e121, 1e122, 1e123, 1e124, 1e125, 1e126, 1e127, 1e128, 1e129, //
    1e130, 1e131, 1e132, 1e133, 1e134, 1e135, 1e136, 1e137, 1e138, 1e139, //
    1e140, 1e141, 1e142, 1e143, 1e144, 1e145, 1e146, 1e147, 1e148, 1e149, //
    1e150, 1e151, 1e152, 1e153, 1e154, 1e155, 1e156, 1e157, 1e158, 1e159, //
    1e160, 1e161, 1e162, 1e163, 1e164, 1e165, 1e166, 1e167, 1e168, 1e169, //
    1e170, 1e171, 1e172, 1e173, 1e174, 1e175, 1e176, 1e177, 1e178, 1e179, //
    1e180, 1e181, 1e182, 1e183, 1e184, 1e185, 1e186, 1e187, 1e188, 1e189, //
    1e190, 1e191, 1e192, 1e193, 1e194, 1e195, 1e196, 1e197, 1e198, 1e199, //
    1e200, 1e201, 1e202, 1e203, 1e204, 1e205, 1e206, 1e207, 1e208, 1e209, //
    1e210, 1e211, 1e212, 1e213, 1e214, 1e215, 1e216, 1e217, 1e218, 1e219, //
    1e220, 1e221, 1e222, 1e223, 1e224, 1e225, 1e226, 1e227, 1e228, 1e229, //
    1e230, 1e231, 1e232, 1e233, 1e234, 1e235, 1e236, 1e237, 1e238, 1e239, //
    1e240, 1e241, 1e242, 1e243, 1e244, 1e245, 1e246, 1e247, 1e248, 1e249, //
    1e250, 1e251, 1e252, 1e253, 1e254, 1e255, 1e256, 1e257, 1e258, 1e259, //
    1e260, 1e261, 1e262, 1e263, 1e264, 1e265, 1e266, 1e267, 1e268, 1e269, //
    1e270, 1e271, 1e272, 1e273, 1e274, 1e275, 1e276, 1e277, 1e278, 1e279, //
    1e280, 1e281, 1e282, 1e283, 1e284, 1e285, 1e286, 1e287, 1e288, 1e289, //
    1e290, 1e291, 1e292, 1e293, 1e294, 1e295, 1e296, 1e297, 1e298, 1e299, //
    1e300, 1e301, 1e302, 1e303, 1e304, 1e305, 1e306, 1e307, 1e308,
];
