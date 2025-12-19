use std::fmt::Debug;

use mathlib::{BigInt, DensePolynomial, FieldConfig, U1024, fp, u1024};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Config17;

impl FieldConfig for Config17 {
    const MODULUS: U1024 = U1024([17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    const MODULUS_BITS: u32 = 1024;
    const R2: U1024 = U1024([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    const N_PRIME: U1024 = U1024([
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
    const ROOT_OF_UNITY: U1024 = U1024([3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn test_gmp_add() {
    let a = u1024!(100) + u1024!(50);
    assert_eq!(a, u1024!(150));
}

#[test]
fn test_gmp_overflow() {
    let mut a = U1024::zero();
    a.0[0] = u64::MAX;

    let b = u1024!(1);
    let (c, carry) = a.carrying_add(&b);

    assert_eq!(c.0[0], 0);
    assert_eq!(c.0[1], 1);
    assert_eq!(carry, false);
}

#[test]
fn test_gmp_mul() {
    // 2^64
    let mut a = U1024::zero();
    a.0[1] = 1;

    // 2^64
    let mut b = U1024::zero();
    b.0[1] = 1;

    // a * b = 2^128.
    let (low, high) = a.full_mul(&b);

    assert_eq!(low.0[2], 1);
    assert_eq!(high, U1024::zero());
}

#[test]
fn test_full_flow() {
    // Uses Config17
    let a = fp!(u1024!(5), Config17);
    let b = fp!(u1024!(7), Config17);
    let prod = a * b;

    assert_eq!(prod.to_u1024().0[0], 1, "Multiplication failed"); // 35 mod 17 = 1
    println!("5 * 7 mod 17 = {:?}", prod);

    let c3 = fp!(u1024!(3), Config17);
    let c2 = fp!(u1024!(2), Config17);

    // DensePolynomial<Config17> inferred
    let poly = DensePolynomial::new(vec![c3, c2]);

    let x = fp!(u1024!(4), Config17);
    let eval = poly.evaluate(&x);

    assert_eq!(eval.to_u1024().0[0], 11, "Poly eval failed");
    println!("P(x) = 3 + 2x at x=4 is {:?}", eval);
}

#[test]
fn test_bit_boundaries() {
    // Test bit 0 (LSB)
    let v = u1024!(1);
    assert!(v.bit(0), "bit 0 should be set");
    assert!(!v.bit(1), "bit 1 should not be set");

    // Test bit 63 (last bit of first limb)
    let mut v = U1024::zero();
    v.0[0] = 1u64 << 63;
    assert!(v.bit(63), "bit 63 should be set");
    assert!(!v.bit(62), "bit 62 should not be set");
    assert!(!v.bit(64), "bit 64 should not be set");

    // Test bit 64 (first bit of second limb)
    let mut v = U1024::zero();
    v.0[1] = 1;
    assert!(v.bit(64), "bit 64 should be set");
    assert!(!v.bit(63), "bit 63 should not be set");
    assert!(!v.bit(65), "bit 65 should not be set");

    // Test bit 1023 (MSB)
    let mut v = U1024::zero();
    v.0[15] = 1u64 << 63;
    assert!(v.bit(1023), "bit 1023 should be set");
    assert!(!v.bit(1022), "bit 1022 should not be set");

    // Test out-of-range indices
    assert!(!v.bit(1024), "bit 1024 should return false (out of range)");
    assert!(!v.bit(1025), "bit 1025 should return false (out of range)");
    assert!(
        !v.bit(usize::MAX),
        "bit usize::MAX should return false (out of range)"
    );

    // Test all bits set
    let mut v = U1024::zero();
    for i in 0..16 {
        v.0[i] = u64::MAX;
    }
    for i in 0..1024 {
        assert!(v.bit(i), "bit {} should be set", i);
    }
    assert!(
        !v.bit(1024),
        "bit 1024 should return false even when all bits are set"
    );
}

#[test]
fn test_from_hex_basic() {
    // Test minimal input
    let v = u1024!("0");
    assert_eq!(v, U1024::zero());

    let v = u1024!("1");
    assert_eq!(v.0[0], 1);

    // Test with 0x prefix
    let v = u1024!("0x1");
    assert_eq!(v.0[0], 1);

    let v = u1024!("0xff");
    assert_eq!(v.0[0], 0xff);
}

#[test]
fn test_from_hex_limb_boundaries() {
    // Test exactly 16 hex digits (one full limb)
    let v = u1024!("0123456789abcdef");
    assert_eq!(v.0[0], 0x0123456789abcdef);
    assert_eq!(v.0[1], 0);

    // Test 17 hex digits (spans two limbs)
    let v = u1024!("10123456789abcdef");
    assert_eq!(v.0[0], 0x0123456789abcdef);
    assert_eq!(v.0[1], 0x1);

    // Test 18 hex digits
    let v = u1024!("ff0000000000000001");
    assert_eq!(v.0[0], 0x0000000000000001);
    assert_eq!(v.0[1], 0xff);

    // Test 32 hex digits (two full limbs)
    let v = u1024!("fedcba9876543210fedcba9876543210");
    assert_eq!(v.0[0], 0xfedcba9876543210);
    assert_eq!(v.0[1], 0xfedcba9876543210);
    assert_eq!(v.0[2], 0);
}

#[test]
fn test_from_hex_max_length() {
    // Test maximum length (256 hex digits = 1024 bits)
    let hex_str = "f".repeat(256);
    let v = u1024!(hex_str.as_str());

    // All limbs should be u64::MAX
    for i in 0..16 {
        assert_eq!(v.0[i], u64::MAX, "limb {} should be u64::MAX", i);
    }
}

#[test]
#[should_panic(expected = "Hex string too long for U1024")]
fn test_from_hex_too_long() {
    // Test string longer than 256 hex digits
    let hex_str = "f".repeat(257);
    u1024!(hex_str.as_str());
}

#[test]
#[should_panic]
fn test_from_hex_invalid_char() {
    // Test invalid hex character
    u1024!("12g4");
}

#[test]
fn test_from_hex_empty() {
    // Empty string should be treated as zero
    let v = u1024!("");
    assert_eq!(v, U1024::zero());
}

#[test]
fn test_from_hex_leading_zeros() {
    // Leading zeros should be handled correctly
    let v = u1024!("00000001");
    assert_eq!(v.0[0], 1);
    assert_eq!(v.0[1], 0);
}

#[test]
fn test_comparison_basic() {
    // Basic comparisons
    let a = u1024!(100);
    let b = u1024!(200);

    assert!(a < b);
    assert!(a <= b);
    assert!(b > a);
    assert!(b >= a);
    assert!(a <= a);
    assert!(a >= a);
}

#[test]
fn test_comparison_equal() {
    let a = u1024!(12345);
    let b = u1024!(12345);

    assert!(a <= b);
    assert!(a >= b);
    assert!(!(a < b));
    assert!(!(a > b));
}

#[test]
fn test_comparison_multi_limb() {
    // Test where difference is in higher limb
    let mut a = U1024::zero();
    a.0[1] = 1; // a = 2^64

    let mut b = U1024::zero();
    b.0[1] = 2; // b = 2 * 2^64

    assert!(a < b);
    assert!(b > a);

    // a has larger low limb but smaller high limb
    let mut c = U1024::zero();
    c.0[0] = u64::MAX;
    c.0[1] = 0;

    let mut d = U1024::zero();
    d.0[0] = 0;
    d.0[1] = 1;

    assert!(c < d, "c should be less than d even though c.0[0] > d.0[0]");
    assert!(d > c);
}

#[test]
fn test_comparison_max_values() {
    // Test with maximum values
    let mut max = U1024::zero();
    for i in 0..16 {
        max.0[i] = u64::MAX;
    }

    let mut almost_max = U1024::zero();
    for i in 0..16 {
        almost_max.0[i] = u64::MAX;
    }
    almost_max.0[15] = u64::MAX - 1;

    assert!(almost_max < max);
    assert!(max > almost_max);

    let zero = U1024::zero();
    assert!(zero < max);
    assert!(max > zero);
}
