use mathlib::field::montgomery::MontgomeryParams;
use mathlib::traits::BigInt;
use mathlib::{DensePolynomial, FieldElement, U1024};

#[test]
fn test_gmp_add() {
    let a = U1024::from_u64(100);
    let b = U1024::from_u64(50);
    let c = a + b;
    assert_eq!(c, U1024::from_u64(150));
}

#[test]
fn test_gmp_overflow() {
    let mut a = U1024::zero();
    a.0[0] = u64::MAX;

    let b = U1024::from_u64(1);
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
    let mut p = U1024::zero();
    p.0[0] = 17;

    let params = MontgomeryParams::new(p, U1024::zero());

    let a = FieldElement::new(U1024::from_u64(5), &params);
    let b = FieldElement::new(U1024::from_u64(7), &params);
    let prod = a * b;

    assert_eq!(prod.to_u1024().0[0], 1, "Multiplication failed");
    println!("5 * 7 mod 17 = {:?}", prod);

    let c3 = FieldElement::new(U1024::from_u64(3), &params);
    let c2 = FieldElement::new(U1024::from_u64(2), &params);

    let poly = DensePolynomial::new(vec![c3, c2]);

    let x = FieldElement::new(U1024::from_u64(4), &params);
    let eval = poly.evaluate(&x);

    assert_eq!(eval.to_u1024().0[0], 11, "Poly eval failed");
    println!("P(x) = 3 + 2x at x=4 is {:?}", eval);
}

#[test]
fn test_bit_boundaries() {
    // Test bit 0 (LSB)
    let v = U1024::from_u64(1);
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
    let v = U1024::from_hex("0");
    assert_eq!(v, U1024::zero());

    let v = U1024::from_hex("1");
    assert_eq!(v.0[0], 1);

    // Test with 0x prefix
    let v = U1024::from_hex("0x1");
    assert_eq!(v.0[0], 1);

    let v = U1024::from_hex("0xff");
    assert_eq!(v.0[0], 0xff);
}

#[test]
fn test_from_hex_limb_boundaries() {
    // Test exactly 16 hex digits (one full limb)
    let v = U1024::from_hex("0123456789abcdef");
    assert_eq!(v.0[0], 0x0123456789abcdef);
    assert_eq!(v.0[1], 0);

    // Test 17 hex digits (spans two limbs)
    let v = U1024::from_hex("10123456789abcdef");
    assert_eq!(v.0[0], 0x0123456789abcdef);
    assert_eq!(v.0[1], 0x1);

    // Test 18 hex digits
    let v = U1024::from_hex("ff0000000000000001");
    assert_eq!(v.0[0], 0x0000000000000001);
    assert_eq!(v.0[1], 0xff);

    // Test 32 hex digits (two full limbs)
    let v = U1024::from_hex("fedcba9876543210fedcba9876543210");
    assert_eq!(v.0[0], 0xfedcba9876543210);
    assert_eq!(v.0[1], 0xfedcba9876543210);
    assert_eq!(v.0[2], 0);
}

#[test]
fn test_from_hex_max_length() {
    // Test maximum length (256 hex digits = 1024 bits)
    let hex_str = "f".repeat(256);
    let v = U1024::from_hex(&hex_str);

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
    U1024::from_hex(&hex_str);
}

#[test]
#[should_panic]
fn test_from_hex_invalid_char() {
    // Test invalid hex character
    U1024::from_hex("12g4");
}

#[test]
fn test_from_hex_empty() {
    // Empty string should be treated as zero
    let v = U1024::from_hex("");
    assert_eq!(v, U1024::zero());
}

#[test]
fn test_from_hex_leading_zeros() {
    // Leading zeros should be handled correctly
    let v = U1024::from_hex("00000001");
    assert_eq!(v.0[0], 1);
    assert_eq!(v.0[1], 0);
}
