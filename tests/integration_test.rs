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

#[test]
fn test_full_flow() {
    let mut p = U1024::zero();
    p.0[0] = 17;
    let params = MontgomeryParams::new(p);

    let a = FieldElement::new(U1024::from_u64(5), &params);
    let b = FieldElement::new(U1024::from_u64(7), &params);

    let prod = a.clone() * b.clone();
    assert_eq!(prod.to_u1024().0[0], 1);
    println!("5 * 7 mod 17 = {:?}", prod);

    let c3 = FieldElement::new(U1024::from_u64(3), &params);
    let c2 = FieldElement::new(U1024::from_u64(2), &params);

    let poly = DensePolynomial::new(vec![c3.clone(), c2.clone()]);

    let x = FieldElement::new(U1024::from_u64(4), &params);
    let eval = poly.evaluate(&x);

    assert_eq!(eval.to_u1024().0[0], 11);
    println!("P(x) = 2x + 3 at x=4 is {:?}", eval);
}
