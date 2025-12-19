use mathlib::{compute_n_prime, compute_r2, u1024};

#[test]
fn test_compute_utilities() {
    // Test with modulus = 17
    let modulus = u1024!(17);

    // Compute R2 and N_PRIME using the exported utilities
    let r2 = compute_r2(&modulus);
    let n_prime = compute_n_prime(&modulus);

    // Verify R2 = 2^2048 mod 17 = 1
    assert_eq!(r2, u1024!(1));

    // Verify N_PRIME (should match the known value for modulus 17)
    let expected_n_prime = mathlib::U1024([
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
    assert_eq!(n_prime, expected_n_prime);
}
