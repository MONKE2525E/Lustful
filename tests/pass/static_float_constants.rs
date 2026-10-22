// Global arrays and promoted aggregates must use C static constants.
static D: [f64; 6] = [0.0, -0.0, f64::from_bits(1), f64::MAX, f64::INFINITY, f64::NEG_INFINITY];
static F: [f32; 6] = [0.0, -0.0, f32::from_bits(1), f32::MAX, f32::INFINITY, f32::NEG_INFINITY];
static P: &(f64, f32) = &(-0.0, f32::from_bits(1));

fn main() {
    assert_eq!(D[0].to_bits(), 0);
    assert_eq!(D[1].to_bits(), 0x8000_0000_0000_0000);
    assert_eq!(D[2].to_bits(), 1);
    assert_eq!(D[3].to_bits(), 0x7fef_ffff_ffff_ffff);
    assert_eq!(D[4].to_bits(), 0x7ff0_0000_0000_0000);
    assert_eq!(D[5].to_bits(), 0xfff0_0000_0000_0000);
    assert_eq!(F[0].to_bits(), 0);
    assert_eq!(F[1].to_bits(), 0x8000_0000);
    assert_eq!(F[2].to_bits(), 1);
    assert_eq!(F[3].to_bits(), 0x7f7f_ffff);
    assert_eq!(F[4].to_bits(), 0x7f80_0000);
    assert_eq!(F[5].to_bits(), 0xff80_0000);
    assert_eq!(P.0.to_bits(), 0x8000_0000_0000_0000);
    assert_eq!(P.1.to_bits(), 1);
}
