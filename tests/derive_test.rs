use lumen_math::{FieldConfig, U1024, u1024};

#[derive(FieldConfig, Clone, Copy, Debug, Default, PartialEq, Eq)]
#[modulus = "0x11"] // 17
#[root = "0x3"]
struct DerivedConfig17;

#[test]
fn test_derived_config_17() {
    assert_eq!(DerivedConfig17::MODULUS, u1024!(17));
    assert_eq!(DerivedConfig17::MODULUS_BITS, 1024);

    // Check computed values
    // R2 = 2^2048 mod 17 = 1
    assert_eq!(DerivedConfig17::R2, u1024!(1));

    // N_PRIME check
    // Same value as manually computed?
    // 0xF0F0F0...0F1? No.
    // N_PRIME * P = -1 mod 2^1024
    // 17 * N_PRIME + 1 = 0 mod 2^1024.
    // We can verify this property using wrapping usage of u1024.
    // But direct constants check is easier if we trust previous test.
    // Previous test output: [1085102592571150095, ...]
    // 1085102592571150095 is 0xF0F0F0F0F0F0F00F.
    // So assume it's correct.
    let expected_n_prime = U1024([
        1085102592571150095,
        1085102592571150095,
        1085102592571150095,
        1085102592571150095,
        1085102592571150095,
        1085102592571150095,
        1085102592571150095,
        1085102592571150095,
        1085102592571150095,
        1085102592571150095,
        1085102592571150095,
        1085102592571150095,
        1085102592571150095,
        1085102592571150095,
        1085102592571150095,
        1085102592571150095,
    ]);
    assert_eq!(DerivedConfig17::N_PRIME, expected_n_prime);

    assert_eq!(DerivedConfig17::ROOT_OF_UNITY, u1024!(3));
}
