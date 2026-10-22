fn observe(text: &str) {
    match serde_json::from_str::<serde_json::Value>(text) {
        Ok(value) => match &value {
            serde_json::Value::Number(n) => println!("{}\tOK\t{}\t{}\t{}\t{:?}\t{:?}\t{:016x}\t{}", text, n.is_i64(), n.is_u64(), n.is_f64(), n.as_i64(), n.as_u64(), n.as_f64().unwrap().to_bits(), serde_json::to_string(&value).unwrap()),
            _ => panic!("generated numeric input returned non-number"),
        },
        Err(error) => println!("{}\tERR\t{}\t{}\t{}", text, error, error.line(), error.column()),
    }
}
fn main() {
    let mut seed = 0xa7139e8426b05cdf_u64;
    for i in 0..3000_u64 {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let a = seed;
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let b = seed;
        let sign = if a & 1 == 0 { "" } else { "-" };
        let exponent = (b % 750) as i64 - 375;
        let text = match i % 6 {
            0 => format!("{}{}e{}", sign, a, exponent),
            1 => format!("{}{}.{}e{}", sign, a, b, exponent),
            2 => format!("{}{}{}{}e{}", sign, a, b, a, exponent),
            3 => format!("{}0.000000000000000000000{}e{}", sign, a, exponent),
            4 => format!("{}{}", sign, a),
            _ => format!("{}{}.000000000000000000000{}E+{}", sign, a, b, b % 400),
        };
        observe(&text);
    }
}
