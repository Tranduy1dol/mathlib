use mathlib::big_int::U1024;
use mathlib::traits::BigInt;

#[test]
fn test_gmp_add() {
    let a = U1024::from_u64(100);
    let b = U1024::from_u64(50);
    let c = a + b;
    assert_eq!(c, U1024::from_u64(150));
}

#[test]
fn test_gmp_overflow() {
    // Test cộng tràn limb đầu tiên
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
