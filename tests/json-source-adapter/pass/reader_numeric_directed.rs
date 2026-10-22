// Same source for the pinned upstream oracle and future Lust reader.
// No float construction/Serialize capability is required: only parsed Value output.
fn main() {
    for text in vectors::NUMBERS {
        match serde_json::from_str::<serde_json::Value>(text) {
            Ok(value) => match &value {
                serde_json::Value::Number(number) => {
                    let f = number.as_f64().expect("finite numeric Value");
                    let encoded = serde_json::to_string(&value).expect("parsed Value write");
                    println!("{}\tOK\ti64={}\tu64={}\tf64={}\ti={:?}\tu={:?}\tbits={:016x}\tjson={}\tdisplay={}\tdebug={:?}",
                        text, number.is_i64(), number.is_u64(), number.is_f64(),
                        number.as_i64(), number.as_u64(), f.to_bits(), encoded, f, f);
                    // Put both parsers' bits on one line; mismatch is evidence,
                    // not a failing assertion or a reason to change oracle features.
                    match text.parse::<f64>() {
                        Ok(s) => println!("{}\tSTD-COMPARE\tjson={:016x}\tstd={:016x}\tequal={}",
                            text, f.to_bits(), s.to_bits(), f.to_bits() == s.to_bits()),
                        Err(_) => println!("{}\tSTD-COMPARE\tERR", text),
                    }
                }
                _ => panic!("numeric corpus unexpectedly produced a non-number"),
            },
            Err(error) => println!("{}\tERR\t{}\tline={}\tcolumn={}",
                text, error, error.line(), error.column()),
        }
    }
}
mod vectors {
// Fixed directed corpus. No expected bits or output bytes are guessed here.
pub const NUMBERS: &[&str] = &[
    "0", "-0", "0.0", "-0.0", "0e0", "-0E+0", "1", "-1", "1.0",
    "1e0", "1E+00", "1e-0", "1.2300", "100000000000000000000.0",
    "9223372036854775807", "9223372036854775808", "-9223372036854775808",
    "-9223372036854775809", "18446744073709551615", "18446744073709551616",
    "9007199254740991", "9007199254740992", "9007199254740993",
    "9007199254740993.0", "0.1", "0.3", "1.234567890123456789",
    "1.234567890123456789012345678901234567890123456789",
    "1234567890123456789012345678901234567890e-30",
    "184467440737095516150000000000000000001e-20",
    "1.00000000000000011102230246251565404236316680908203125",
    "1.00000000000000011102230246251565404236316680908203126",
    "2.2250738585072014e-308", "2.2250738585072011e-308",
    "4.9406564584124654e-324", "5e-324", "2.4703282292062327e-324",
    "2.4703282292062328e-324", "1e-324", "-1e-324", "1e-400", "-1e-400",
    "1.7976931348623157e308", "1.7976931348623158e308",
    "1.7976931348623159e308", "1e309", "-1e309",
    "0e999999999999999999999999", "-0e999999999999999999999999",
    "1e999999999999999999999999", "1e-999999999999999999999999",
    "-1e-999999999999999999999999",
    "1e-7", "1e-6", "1e-5", "1e15", "1e16", "1e20", "1e21", "1e22",
    "1E+023", "1e+003", "-1E-007",
    // JSON grammar controls; std parse may accept some of these by design.
    "+1", "01", "-01", ".1", "1.", "1e", "1e+", "--1", "NaN", "inf",
    "Infinity", "1_0", "1 2", "0x10", "", " 1 ", "1e309x",
];

}
