use lumen_math::{BigInt, U1024, u1024};

#[test]
fn test_u1024_const_add() {
    let a = U1024([100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U1024([50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);

    let (sum, carry) = a.const_add(&b);
    assert_eq!(sum.0[0], 150);
    assert!(!carry);
}

#[test]
fn test_u1024_const_add_with_carry() {
    let a = U1024([u64::MAX, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U1024([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);

    let (sum, _carry) = a.const_add(&b);
    assert_eq!(sum.0[0], 0);
    assert_eq!(sum.0[1], 1);
}

#[test]
fn test_u1024_const_sub() {
    let a = U1024([100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U1024([50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);

    let (diff, borrow) = a.const_sub(&b);
    assert_eq!(diff.0[0], 50);
    assert!(!borrow);
}

#[test]
fn test_u1024_const_sub_with_borrow() {
    let a = U1024([0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U1024([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);

    let (diff, _borrow) = a.const_sub(&b);
    assert_eq!(diff.0[0], u64::MAX);
    assert_eq!(diff.0[1], 0);
}

#[test]
fn test_u1024_const_mul() {
    let a = U1024([123, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U1024([456, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);

    let (low, _high) = a.const_mul(&b);
    assert_eq!(low.0[0], 123 * 456);
}

#[test]
fn test_u1024_const_eq() {
    let a = U1024([1, 2, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U1024([1, 2, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    let c = U1024([1, 2, 3, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);

    assert!(a.const_eq(&b));
    assert!(!a.const_eq(&c));
}

#[test]
fn test_u1024_comparison_operators() {
    let a = u1024!(100);
    let b = u1024!(200);
    let c = u1024!(100);

    assert!(a < b);
    assert!(!(b < a));
    assert!(a <= c);
    assert!(a >= c);
    assert!(!(a > c));
}

#[test]
fn test_u1024_bit_operations() {
    let mut val = U1024::zero();
    val.0[0] = 0b1010;

    assert!(val.bit(1));
    assert!(!val.bit(0));
    assert!(val.bit(3));
    assert!(!val.bit(2));
}

#[test]
fn test_u1024_bit_high_positions() {
    let mut val = U1024::zero();
    val.0[15] = 1u64 << 63; // Set the highest bit

    assert!(val.bit(1023));
    assert!(!val.bit(1022));
    assert!(!val.bit(0));
}

#[test]
fn test_u1024_from_conversions() {
    assert_eq!(U1024::from_u8(255), u1024!(255));
    assert_eq!(U1024::from_u16(65535), u1024!(65535));
    assert_eq!(U1024::from_u32(u32::MAX), u1024!(u32::MAX as u64));
    assert_eq!(
        U1024::from_u64(u64::MAX),
        U1024([u64::MAX, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    );
}

#[test]
fn test_u1024_from_u128() {
    let val = u128::MAX;
    let result = U1024::from_u128(val);

    assert_eq!(result.0[0], u64::MAX);
    assert_eq!(result.0[1], u64::MAX);
    assert_eq!(result.0[2], 0);
}

#[test]
fn test_u1024_xor() {
    let a = U1024([
        0xAAAAAAAAAAAAAAAA,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ]);
    let b = U1024([
        0x5555555555555555,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ]);

    let result = a ^ b;
    assert_eq!(result.0[0], 0xFFFFFFFFFFFFFFFF);
}

#[test]
fn test_u1024_add_operator() {
    let a = u1024!(100);
    let b = u1024!(50);

    let sum = a + b;
    assert_eq!(sum, u1024!(150));
}

#[test]
fn test_u1024_sub_operator() {
    let a = u1024!(100);
    let b = u1024!(50);

    let (diff, borrow) = a.borrowing_sub(&b);
    assert_eq!(diff, u1024!(50));
    assert!(!borrow);
}

#[test]
fn test_u1024_carrying_add() {
    let mut a = U1024::zero();
    a.0[0] = u64::MAX;
    let b = u1024!(2);

    let (sum, carry) = a.carrying_add(&b);
    assert_eq!(sum.0[0], 1);
    assert_eq!(sum.0[1], 1);
    assert!(!carry);
}

#[test]
fn test_u1024_bits_count() {
    let val = u1024!(255); // 0xFF = 8 bits
    assert!(val.bits() <= 8);

    let big_val = U1024([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]);
    assert!(big_val.bits() > 960); // Should be close to 960
}

#[test]
fn test_u1024_zero_and_one() {
    let zero = U1024::zero();
    let one = U1024::one();

    assert_eq!(zero.0[0], 0);
    assert_eq!(one.0[0], 1);

    for i in 1..16 {
        assert_eq!(zero.0[i], 0);
        assert_eq!(one.0[i], 0);
    }
}

#[test]
fn test_u1024_full_mul() {
    let a = U1024([2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U1024([3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);

    let (low, high) = a.full_mul(&b);
    assert_eq!(low.0[0], 6);
    assert_eq!(high.0[0], 0);
}

#[test]
fn test_u1024_to_le_bytes_roundtrip() {
    let original = U1024([
        0x0102030405060708,
        0x1112131415161718,
        0x2122232425262728,
        0x3132333435363738,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ]);

    let bytes = original.to_le_bytes();
    let recovered = U1024::from_le_bytes(&bytes);

    assert_eq!(original, recovered);
}

#[test]
fn test_u1024_to_be_bytes_roundtrip() {
    let original = U1024([
        0x0102030405060708,
        0x1112131415161718,
        0x2122232425262728,
        0x3132333435363738,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ]);

    let bytes = original.to_be_bytes();
    let recovered = U1024::from_be_bytes(&bytes);

    assert_eq!(original, recovered);
}

#[test]
fn test_u1024_to_le_bytes_values() {
    let val = U1024::from_le_bytes(&[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]);
    let bytes = val.to_le_bytes();

    // First 8 bytes should match input
    assert_eq!(bytes[0], 0x01);
    assert_eq!(bytes[1], 0x02);
    assert_eq!(bytes[7], 0x08);

    // Rest should be zero
    assert_eq!(bytes[8], 0x00);
}

#[test]
fn test_u1024_to_be_bytes_values() {
    // 8 bytes in big endian, should appear at the END of the 128-byte array
    let val = U1024::from_be_bytes(&[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]);
    let bytes = val.to_be_bytes();

    // Last 8 bytes should match input
    assert_eq!(bytes[120], 0x01);
    assert_eq!(bytes[121], 0x02);
    assert_eq!(bytes[127], 0x08);

    // First bytes should be zero
    assert_eq!(bytes[0], 0x00);
}

#[test]
fn test_u1024_shift_left() {
    let a = u1024!(1u64);
    assert_eq!(a << 0, a);
    assert_eq!(a << 1, u1024!(2u64));
    assert_eq!(a << 10, u1024!(1024u64));

    // Shift across limb boundary (64 bits)
    let b = u1024!(1u64);
    let shifted = b << 64;
    assert_eq!(shifted.0[0], 0);
    assert_eq!(shifted.0[1], 1);

    // Shift large amount
    let c = u1024!(1u64);
    let large_shift = c << 1000;
    assert!(large_shift > u1024!(0));
    assert_eq!(large_shift.bits(), 1001);
}

#[test]
fn test_u1024_shift_right() {
    let a = u1024!(1024u64);
    assert_eq!(a >> 0, a);
    assert_eq!(a >> 1, u1024!(512u64));
    assert_eq!(a >> 10, u1024!(1u64));

    // Shift across limb boundary
    let mut b = U1024::zero();
    b.0[1] = 1; // 2^64
    let shifted = b >> 64;
    assert_eq!(shifted, u1024!(1u64));

    // Shift large amount
    // Construct MAX manually
    let c = U1024([u64::MAX; 16]);
    let zero = c >> 1024;
    assert_eq!(zero, U1024::ZERO);
}

#[test]
fn test_u1024_with_bit() {
    let a = U1024::ZERO;
    let b = a.with_bit(0);
    assert_eq!(b, u1024!(1u64));

    let c = a.with_bit(64);
    assert_eq!(c.0[1], 1);
    assert_eq!(c.0[0], 0);

    let d = a.with_bit(1023);
    assert!(d.bit(1023));
}

#[test]
fn test_u1024_div_rem() {
    let a = u1024!(100u64);
    let b = u1024!(25u64);
    let (q, r) = a.div_rem(&b);
    assert_eq!(q, u1024!(4u64));
    assert_eq!(r, U1024::ZERO);

    let c = u1024!(100u64);
    let d = u1024!(30u64);
    let (q2, r2) = c.div_rem(&d);
    assert_eq!(q2, u1024!(3u64)); // 3 * 30 = 90
    assert_eq!(r2, u1024!(10u64)); // 100 - 90 = 10
}

#[test]
#[should_panic(expected = "Division by zero")]
fn test_u1024_div_rem_zero_panic() {
    let a = u1024!(100u64);
    let b = U1024::ZERO;
    a.div_rem(&b);
}

#[test]
fn test_u1024_div_rem_edge() {
    // Divide by larger number
    let a = u1024!(10u64);
    let b = u1024!(20u64);
    let (q, r) = a.div_rem(&b);
    assert_eq!(q, U1024::ZERO);
    assert_eq!(r, a);

    // Divide max
    let max = U1024([u64::MAX; 16]);
    let (q2, r2) = max.div_rem(&u1024!(2u64));
    // q2 should be max >> 1
    assert_eq!(q2, max >> 1);
    assert_eq!(r2, u1024!(1u64)); // max is odd
}
