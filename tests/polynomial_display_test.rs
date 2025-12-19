use mathlib::{DensePolynomial, fp};

#[test]
fn test_polynomial_display_format() {
    // P(x) = 3x^2 + 2x + 1
    let poly = DensePolynomial::new(vec![fp!(1u64), fp!(2u64), fp!(3u64)]);
    let display = format!("{}", poly);
    assert_eq!(display, "3x^2 + 2x + 1");

    // P(x) = x^3 + 5
    let poly2 = DensePolynomial::new(vec![fp!(5u64), fp!(0u64), fp!(0u64), fp!(1u64)]);
    let display2 = format!("{}", poly2);
    assert_eq!(display2, "x^3 + 5");

    // P(x) = x (coefficient 1 should not be shown)
    let poly3 = DensePolynomial::new(vec![fp!(0u64), fp!(1u64)]);
    let display3 = format!("{}", poly3);
    assert_eq!(display3, "x");

    // P(x) = 0
    let poly_zero = DensePolynomial::new(vec![fp!(0u64)]);
    let display_zero = format!("{}", poly_zero);
    assert_eq!(display_zero, "0");
}

#[test]
fn test_polynomial_debug_format() {
    let poly = DensePolynomial::new(vec![fp!(1u64), fp!(2u64), fp!(3u64)]);
    let debug = format!("{:?}", poly);

    // Debug format should show Poly(...mathematical notation...)
    assert!(debug.starts_with("Poly("));
    assert!(debug.contains("3x^2"));
}
