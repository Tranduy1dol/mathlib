use mathlib::{DefaultFieldConfig, DensePolynomial, fp};

#[test]
fn test_polynomial_addition() {
    let p1 = DensePolynomial::new(vec![fp!(1u64), fp!(2u64), fp!(3u64)]);
    let p2 = DensePolynomial::new(vec![fp!(4u64), fp!(5u64)]);

    let sum = p1.clone() + p2.clone();

    // (1 + 2x + 3x^2) + (4 + 5x) = 5 + 7x + 3x^2
    assert_eq!(sum.coeffs.len(), 3);
    assert_eq!(sum.coeffs[0].to_u1024(), fp!(5u64).to_u1024());
    assert_eq!(sum.coeffs[1].to_u1024(), fp!(7u64).to_u1024());
    assert_eq!(sum.coeffs[2].to_u1024(), fp!(3u64).to_u1024());
}

#[test]
fn test_polynomial_addition_different_sizes() {
    let p1 = DensePolynomial::new(vec![fp!(1u64)]);
    let p2 = DensePolynomial::new(vec![fp!(2u64), fp!(3u64), fp!(4u64)]);

    let sum = p1 + p2;
    assert_eq!(sum.coeffs.len(), 3);
}

#[test]
fn test_polynomial_multiplication_naive() {
    let p1 = DensePolynomial::new(vec![fp!(1u64), fp!(2u64)]);
    let p2 = DensePolynomial::new(vec![fp!(3u64), fp!(4u64)]);

    let prod = p1 * p2;

    // (1 + 2x) * (3 + 4x) = 3 + 10x + 8x^2
    assert_eq!(prod.coeffs.len(), 3);
    assert_eq!(prod.coeffs[0].to_u1024(), fp!(3u64).to_u1024());
    assert_eq!(prod.coeffs[1].to_u1024(), fp!(10u64).to_u1024());
    assert_eq!(prod.coeffs[2].to_u1024(), fp!(8u64).to_u1024());
}

#[test]
fn test_polynomial_multiplication_with_zero() {
    let zero_poly = DensePolynomial::<DefaultFieldConfig>::zero();
    let p = DensePolynomial::new(vec![fp!(1u64), fp!(2u64)]);

    let prod = zero_poly * p;
    assert!(prod.coeffs.is_empty());
}

#[test]
fn test_polynomial_evaluation() {
    // P(x) = 2 + 3x + 4x^2
    let poly = DensePolynomial::new(vec![fp!(2u64), fp!(3u64), fp!(4u64)]);

    // P(0) = 2
    let x0 = fp!(0u64);
    let y0 = poly.evaluate(&x0);
    assert_eq!(y0.to_u1024(), fp!(2u64).to_u1024());

    // P(1) = 2 + 3 + 4 = 9
    let x1 = fp!(1u64);
    let y1 = poly.evaluate(&x1);
    assert_eq!(y1.to_u1024(), fp!(9u64).to_u1024());
}

#[test]
fn test_polynomial_evaluation_at_zero() {
    let poly = DensePolynomial::new(vec![fp!(42u64), fp!(10u64), fp!(5u64)]);
    let x = fp!(0u64);
    let y = poly.evaluate(&x);

    // P(0) should be the constant term
    assert_eq!(y.to_u1024(), fp!(42u64).to_u1024());
}

#[test]
fn test_polynomial_zero() {
    let zero = DensePolynomial::<DefaultFieldConfig>::zero();
    assert!(zero.coeffs.is_empty());
}

#[test]
fn test_polynomial_trim() {
    // Create polynomial with trailing zeros
    let poly = DensePolynomial::new(vec![fp!(1u64), fp!(2u64), fp!(0u64), fp!(0u64)]);

    // Trailing zeros should be removed
    assert_eq!(poly.coeffs.len(), 2);
}

#[test]
fn test_polynomial_mul_fast_vs_naive() {
    let p1 = DensePolynomial::new(vec![fp!(1u64), fp!(2u64), fp!(3u64)]);
    let p2 = DensePolynomial::new(vec![fp!(4u64), fp!(5u64)]);

    let naive_result = p1.clone() * p2.clone();
    let fast_result = p1.mul_fast(&p2);

    // Both methods should give the same result
    assert_eq!(naive_result.coeffs.len(), fast_result.coeffs.len());
    for (a, b) in naive_result.coeffs.iter().zip(fast_result.coeffs.iter()) {
        assert_eq!(a.to_u1024(), b.to_u1024());
    }
}

#[test]
fn test_polynomial_mul_fast_larger() {
    // Create larger polynomials to test NTT
    let size = 16;
    let coeffs1: Vec<_> = (0..size).map(|i| fp!(i as u64)).collect();
    let coeffs2: Vec<_> = (0..size).map(|i| fp!((i + 1) as u64)).collect();

    let p1 = DensePolynomial::new(coeffs1);
    let p2 = DensePolynomial::new(coeffs2);

    let naive_result = p1.clone() * p2.clone();
    let fast_result = p1.mul_fast(&p2);

    // Results should match
    assert_eq!(naive_result.coeffs.len(), fast_result.coeffs.len());
    for (a, b) in naive_result.coeffs.iter().zip(fast_result.coeffs.iter()) {
        assert_eq!(a.to_u1024(), b.to_u1024());
    }
}

#[test]
fn test_polynomial_addition_commutativity() {
    let p1 = DensePolynomial::new(vec![fp!(1u64), fp!(2u64)]);
    let p2 = DensePolynomial::new(vec![fp!(3u64), fp!(4u64)]);

    let sum1 = p1.clone() + p2.clone();
    let sum2 = p2 + p1;

    assert_eq!(sum1.coeffs.len(), sum2.coeffs.len());
    for (a, b) in sum1.coeffs.iter().zip(sum2.coeffs.iter()) {
        assert_eq!(a.to_u1024(), b.to_u1024());
    }
}

#[test]
fn test_polynomial_clone() {
    let poly = DensePolynomial::new(vec![fp!(1u64), fp!(2u64), fp!(3u64)]);
    let cloned = poly.clone();

    assert_eq!(poly.coeffs.len(), cloned.coeffs.len());
    for (a, b) in poly.coeffs.iter().zip(cloned.coeffs.iter()) {
        assert_eq!(a.to_u1024(), b.to_u1024());
    }
}

#[test]
fn test_polynomial_debug_format() {
    let poly = DensePolynomial::new(vec![fp!(1u64), fp!(2u64)]);
    let debug_str = format!("{:?}", poly);

    assert!(debug_str.starts_with("Poly"));
}
