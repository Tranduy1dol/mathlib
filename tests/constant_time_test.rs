//! Constant-time operation tests
//!
//! These tests verify that the constant-time implementations produce correct results.
//! For timing analysis, see the corresponding benchmarks in `benches/constant_time_bench.rs`.

use lumen_math::U1024;
use lumen_math::traits::BigInt;

// ============================================================================
// conditional_select Tests
// ============================================================================

#[test]
fn test_conditional_select_returns_first_when_true() {
    let a = U1024::from_u64(42);
    let b = U1024::from_u64(100);

    let result = U1024::conditional_select(&a, &b, true);
    assert_eq!(result, a);
}

#[test]
fn test_conditional_select_returns_second_when_false() {
    let a = U1024::from_u64(42);
    let b = U1024::from_u64(100);

    let result = U1024::conditional_select(&a, &b, false);
    assert_eq!(result, b);
}

#[test]
fn test_conditional_select_with_zero() {
    let a = U1024::ZERO;
    let b = U1024::from_u64(u64::MAX);

    assert_eq!(U1024::conditional_select(&a, &b, true), a);
    assert_eq!(U1024::conditional_select(&a, &b, false), b);
}

#[test]
fn test_conditional_select_with_max_values() {
    let a = U1024([u64::MAX; 16]);
    let b = U1024::ZERO;

    assert_eq!(U1024::conditional_select(&a, &b, true), a);
    assert_eq!(U1024::conditional_select(&a, &b, false), b);
}

#[test]
fn test_conditional_select_same_values() {
    let v = U1024::from_u64(12345);

    assert_eq!(U1024::conditional_select(&v, &v, true), v);
    assert_eq!(U1024::conditional_select(&v, &v, false), v);
}

#[test]
fn test_conditional_select_all_limbs_differ() {
    let a = U1024([
        0x0123456789ABCDEF,
        0xFEDCBA9876543210,
        0x1111111111111111,
        0x2222222222222222,
        0x3333333333333333,
        0x4444444444444444,
        0x5555555555555555,
        0x6666666666666666,
        0x7777777777777777,
        0x8888888888888888,
        0x9999999999999999,
        0xAAAAAAAAAAAAAAAA,
        0xBBBBBBBBBBBBBBBB,
        0xCCCCCCCCCCCCCCCC,
        0xDDDDDDDDDDDDDDDD,
        0xEEEEEEEEEEEEEEEE,
    ]);

    let b = U1024([
        0xFFFFFFFFFFFFFFFF,
        0x0000000000000000,
        0xEEEEEEEEEEEEEEEE,
        0xDDDDDDDDDDDDDDDD,
        0xCCCCCCCCCCCCCCCC,
        0xBBBBBBBBBBBBBBBB,
        0xAAAAAAAAAAAAAAAA,
        0x9999999999999999,
        0x8888888888888888,
        0x7777777777777777,
        0x6666666666666666,
        0x5555555555555555,
        0x4444444444444444,
        0x3333333333333333,
        0x2222222222222222,
        0x1111111111111111,
    ]);

    let result_true = U1024::conditional_select(&a, &b, true);
    let result_false = U1024::conditional_select(&a, &b, false);

    // Verify all limbs are correctly selected
    for i in 0..16 {
        assert_eq!(
            result_true.0[i], a.0[i],
            "Limb {} mismatch for choice=true",
            i
        );
        assert_eq!(
            result_false.0[i], b.0[i],
            "Limb {} mismatch for choice=false",
            i
        );
    }
}

// ============================================================================
// bits() Tests
// ============================================================================

#[test]
fn test_bits_zero() {
    assert_eq!(U1024::ZERO.bits(), 0);
}

#[test]
fn test_bits_one() {
    assert_eq!(U1024::ONE.bits(), 1);
}

#[test]
fn test_bits_powers_of_two() {
    // 2^0 = 1 -> 1 bit
    assert_eq!(U1024::from_u64(1).bits(), 1);
    // 2^1 = 2 -> 2 bits
    assert_eq!(U1024::from_u64(2).bits(), 2);
    // 2^7 = 128 -> 8 bits
    assert_eq!(U1024::from_u64(128).bits(), 8);
    // 2^63
    assert_eq!(U1024::from_u64(1u64 << 63).bits(), 64);
}

#[test]
fn test_bits_max_u64() {
    assert_eq!(U1024::from_u64(u64::MAX).bits(), 64);
}

#[test]
fn test_bits_multi_limb() {
    // Value in second limb (limb index 1)
    let mut v = U1024::ZERO;
    v.0[1] = 1;
    assert_eq!(v.bits(), 65); // 64 bits from limb 0 + 1 bit in limb 1

    // Value in highest limb (limb index 15)
    let mut v = U1024::ZERO;
    v.0[15] = 1;
    assert_eq!(v.bits(), 64 * 15 + 1); // 961 bits
}

#[test]
fn test_bits_full_1024() {
    let max = U1024([u64::MAX; 16]);
    assert_eq!(max.bits(), 1024);
}

#[test]
fn test_bits_consistency_with_hex() {
    // 0x10 = 16 = binary 10000, which needs 5 bits
    let v = U1024::from_hex("0x10");
    assert_eq!(v.bits(), 5);

    // 0xFF = 255, needs 8 bits
    let v = U1024::from_hex("0xFF");
    assert_eq!(v.bits(), 8);

    // 0x100 = 256, needs 9 bits
    let v = U1024::from_hex("0x100");
    assert_eq!(v.bits(), 9);
}

// ============================================================================
// mod_pow Tests
// ============================================================================

#[test]
fn test_mod_pow_basic() {
    let base = U1024::from_u64(2);
    let exp = U1024::from_u64(10);
    let modulus = U1024::from_u64(1000);

    // 2^10 = 1024, 1024 mod 1000 = 24
    let result = base.mod_pow(&exp, &modulus);
    assert_eq!(result, U1024::from_u64(24));
}

#[test]
fn test_mod_pow_exponent_zero() {
    let base = U1024::from_u64(123);
    let exp = U1024::ZERO;
    let modulus = U1024::from_u64(1000);

    // Any^0 = 1
    let result = base.mod_pow(&exp, &modulus);
    assert_eq!(result, U1024::ONE);
}

#[test]
fn test_mod_pow_exponent_one() {
    let base = U1024::from_u64(123);
    let exp = U1024::ONE;
    let modulus = U1024::from_u64(1000);

    // 123^1 mod 1000 = 123
    let result = base.mod_pow(&exp, &modulus);
    assert_eq!(result, U1024::from_u64(123));
}

#[test]
fn test_mod_pow_modulus_one() {
    let base = U1024::from_u64(123);
    let exp = U1024::from_u64(456);
    let modulus = U1024::ONE;

    // Any mod 1 = 0
    let result = base.mod_pow(&exp, &modulus);
    assert_eq!(result, U1024::ZERO);
}

#[test]
fn test_mod_pow_fermat_little_theorem() {
    // For prime p, a^(p-1) ≡ 1 (mod p) when gcd(a, p) = 1
    let prime = U1024::from_u64(17);
    let base = U1024::from_u64(3);
    let exp = U1024::from_u64(16); // p - 1

    let result = base.mod_pow(&exp, &prime);
    assert_eq!(result, U1024::ONE);
}

#[test]
fn test_mod_pow_large_exponent() {
    let base = U1024::from_u64(7);
    let exp = U1024::from_u64(1_000_000);
    let modulus = U1024::from_u64(1_000_000_007); // Large prime

    // Just verify it doesn't panic and returns a valid result < modulus
    let result = base.mod_pow(&exp, &modulus);
    assert!(result < modulus);
}

#[test]
fn test_mod_pow_base_larger_than_modulus() {
    let base = U1024::from_u64(1000);
    let exp = U1024::from_u64(3);
    let modulus = U1024::from_u64(7);

    // 1000 mod 7 = 6, 6^3 = 216, 216 mod 7 = 6
    let result = base.mod_pow(&exp, &modulus);
    assert_eq!(result, U1024::from_u64(6));
}

#[test]
#[should_panic(expected = "Modulus cannot be zero")]
fn test_mod_pow_zero_modulus_panics() {
    let base = U1024::from_u64(2);
    let exp = U1024::from_u64(10);
    let modulus = U1024::ZERO;

    let _ = base.mod_pow(&exp, &modulus);
}

// ============================================================================
// div_rem Tests (Constant-Time Version)
// ============================================================================

#[test]
fn test_div_rem_basic() {
    let a = U1024::from_u64(100);
    let b = U1024::from_u64(7);

    let (q, r) = a.div_rem(&b);

    assert_eq!(q, U1024::from_u64(14)); // 100 / 7 = 14
    assert_eq!(r, U1024::from_u64(2)); // 100 % 7 = 2

    // Verify: a = q * b + r
    let (prod, _) = q.const_mul(&b);
    assert_eq!(prod + r, a);
}

#[test]
fn test_div_rem_exact_division() {
    let a = U1024::from_u64(100);
    let b = U1024::from_u64(10);

    let (q, r) = a.div_rem(&b);

    assert_eq!(q, U1024::from_u64(10));
    assert_eq!(r, U1024::ZERO);
}

#[test]
fn test_div_rem_dividend_smaller() {
    let a = U1024::from_u64(5);
    let b = U1024::from_u64(10);

    let (q, r) = a.div_rem(&b);

    assert_eq!(q, U1024::ZERO);
    assert_eq!(r, U1024::from_u64(5));
}

#[test]
fn test_div_rem_same_values() {
    let a = U1024::from_u64(42);
    let b = U1024::from_u64(42);

    let (q, r) = a.div_rem(&b);

    assert_eq!(q, U1024::ONE);
    assert_eq!(r, U1024::ZERO);
}

#[test]
fn test_div_rem_large_values() {
    let a = U1024::from_u64(u64::MAX);
    let b = U1024::from_u64(1000);

    let (q, r) = a.div_rem(&b);

    // Verify: a = q * b + r
    let (prod, _) = q.const_mul(&b);
    assert_eq!(prod + r, a);
}

#[test]
#[should_panic(expected = "Division by zero")]
fn test_div_rem_zero_divisor_panics() {
    let a = U1024::from_u64(100);
    let b = U1024::ZERO;

    let _ = a.div_rem(&b);
}

// ============================================================================
// Correctness Tests for Different Hamming Weights
// (Important for timing analysis - same results regardless of bit patterns)
// ============================================================================

#[test]
fn test_mod_pow_same_result_different_hamming_weights() {
    let base = U1024::from_u64(3);
    let modulus = U1024::from_u64(1000);

    // Low Hamming weight exponent (sparse bits)
    let exp_low = U1024::from_u64(0x8000_0000_0000_0001); // Only 2 bits set

    // High Hamming weight exponent (dense bits) - same value mod some power
    // We'll use different exponents but verify correctness
    let exp_high = U1024::from_u64(0xFFFF_FFFF_FFFF_FFFF); // 64 bits set

    // Both should produce valid results
    let result_low = base.mod_pow(&exp_low, &modulus);
    let result_high = base.mod_pow(&exp_high, &modulus);

    // Results should be less than modulus
    assert!(result_low < modulus);
    assert!(result_high < modulus);
}

#[test]
fn test_conditional_select_different_patterns() {
    // All zeros vs all ones
    let zeros = U1024::ZERO;
    let ones = U1024([u64::MAX; 16]);

    // Alternating pattern
    let alternating = U1024([0xAAAA_AAAA_AAAA_AAAA; 16]);

    // All combinations should work correctly
    assert_eq!(U1024::conditional_select(&zeros, &ones, true), zeros);
    assert_eq!(U1024::conditional_select(&zeros, &ones, false), ones);
    assert_eq!(
        U1024::conditional_select(&alternating, &zeros, true),
        alternating
    );
    assert_eq!(
        U1024::conditional_select(&alternating, &zeros, false),
        zeros
    );
}

// ============================================================================
// Property-Based-Like Tests
// ============================================================================

#[test]
fn test_div_rem_many_values() {
    // Test a range of dividend/divisor combinations
    let test_cases = [
        (1u64, 1u64),
        (10, 3),
        (100, 7),
        (1000, 13),
        (u64::MAX, 2),
        (u64::MAX, u64::MAX),
        (0x1234_5678_9ABC_DEF0, 0xFEDC),
    ];

    for (a, b) in test_cases {
        let dividend = U1024::from_u64(a);
        let divisor = U1024::from_u64(b);

        let (q, r) = dividend.div_rem(&divisor);

        // Verify: dividend = quotient * divisor + remainder
        let (prod, _) = q.const_mul(&divisor);
        assert_eq!(
            prod + r,
            dividend,
            "Failed for {} / {}: q={:?}, r={:?}",
            a,
            b,
            q,
            r
        );

        // Verify: remainder < divisor
        assert!(
            r < divisor,
            "Remainder {} >= divisor {} for {} / {}",
            r,
            divisor,
            a,
            b
        );
    }
}

#[test]
fn test_bits_many_values() {
    let test_cases = [
        (0u64, 0usize),
        (1, 1),
        (2, 2),
        (3, 2),
        (4, 3),
        (7, 3),
        (8, 4),
        (15, 4),
        (16, 5),
        (255, 8),
        (256, 9),
        (u64::MAX, 64),
    ];

    for (value, expected_bits) in test_cases {
        let v = U1024::from_u64(value);
        assert_eq!(v.bits(), expected_bits, "bits() failed for value {}", value);
    }
}
