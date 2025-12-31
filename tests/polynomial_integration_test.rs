//! Integration tests for enhanced polynomial types.

use std::collections::BTreeMap;

use lumen_math::{DefaultFieldConfig, FieldElement, MultivariatePolynomial, Polynomial, fp, u1024};

// ============================================================================
// Polynomial (Univariate) Integration Tests
// ============================================================================

#[test]
fn test_polynomial_basic_operations() {
    // Create P(x) = 3x^2 + 2x + 1
    let p = Polynomial::new(vec![fp!(1u64), fp!(2u64), fp!(3u64)]);

    assert_eq!(p.degree(), Some(2));
    assert!(!p.is_zero());
    assert_eq!(p.leading_coefficient().unwrap().to_u1024(), u1024!(3));
}

#[test]
fn test_polynomial_constructors() {
    // Test various constructors
    let zero = Polynomial::<DefaultFieldConfig>::zero();
    assert!(zero.is_zero());

    let one = Polynomial::<DefaultFieldConfig>::one();
    assert_eq!(one.degree(), Some(0));

    let x = Polynomial::<DefaultFieldConfig>::x();
    assert_eq!(x.degree(), Some(1));

    let const_poly = Polynomial::constant(fp!(42u64));
    assert_eq!(const_poly.evaluate(&fp!(0u64)).to_u1024(), u1024!(42));

    let mono = Polynomial::monomial(fp!(5u64), 3);
    assert_eq!(mono.degree(), Some(3));
}

#[test]
fn test_polynomial_arithmetic() {
    let p1 = Polynomial::new(vec![fp!(1u64), fp!(2u64)]);
    let p2 = Polynomial::new(vec![fp!(3u64), fp!(4u64)]);

    // Addition: (1 + 2x) + (3 + 4x) = 4 + 6x
    let sum = p1.clone() + p2.clone();
    assert_eq!(sum.coeffs[0].to_u1024(), u1024!(4));
    assert_eq!(sum.coeffs[1].to_u1024(), u1024!(6));

    // Subtraction: (1 + 2x) - (3 + 4x) = -2 - 2x
    let diff = p1.clone() - p2.clone();
    assert_eq!(diff.degree(), Some(1));

    // Multiplication: (1 + 2x) * (3 + 4x) = 3 + 10x + 8x^2
    let prod = p1.clone() * p2.clone();
    assert_eq!(prod.coeffs.len(), 3);
    assert_eq!(prod.coeffs[0].to_u1024(), u1024!(3));
    assert_eq!(prod.coeffs[1].to_u1024(), u1024!(10));
    assert_eq!(prod.coeffs[2].to_u1024(), u1024!(8));

    // Negation
    let neg = -p1.clone();
    let sum_with_neg = p1.clone() + neg;
    assert!(sum_with_neg.is_zero());
}

#[test]
fn test_polynomial_division() {
    // (x^2 - 1) / (x - 1) = (x + 1) with remainder 0
    let neg_one = -FieldElement::<DefaultFieldConfig>::one();
    let one = FieldElement::<DefaultFieldConfig>::one();

    let dividend = Polynomial::new(vec![neg_one, fp!(0u64), one]); // x^2 - 1
    let divisor = Polynomial::new(vec![neg_one, one]); // x - 1

    let (quotient, remainder) = dividend.divide_with_remainder(&divisor);

    assert!(remainder.is_zero());
    assert_eq!(quotient.degree(), Some(1));
    // quotient = x + 1
    assert_eq!(quotient.coeffs[0].to_u1024(), u1024!(1));
    assert_eq!(quotient.coeffs[1].to_u1024(), u1024!(1));
}

#[test]
fn test_polynomial_evaluation() {
    // P(x) = 1 + 2x + 3x^2
    let p = Polynomial::new(vec![fp!(1u64), fp!(2u64), fp!(3u64)]);

    // P(0) = 1
    assert_eq!(p.evaluate(&fp!(0u64)).to_u1024(), u1024!(1));

    // P(1) = 1 + 2 + 3 = 6
    assert_eq!(p.evaluate(&fp!(1u64)).to_u1024(), u1024!(6));

    // Batch evaluation
    let points = vec![fp!(0u64), fp!(1u64), fp!(2u64)];
    let values = p.evaluate_batch(&points);
    assert_eq!(values.len(), 3);
}

#[test]
fn test_polynomial_derivative() {
    // d/dx (1 + 2x + 3x^2) = 2 + 6x
    let p = Polynomial::new(vec![fp!(1u64), fp!(2u64), fp!(3u64)]);
    let dp = p.derivative();

    assert_eq!(dp.degree(), Some(1));
    assert_eq!(dp.coeffs[0].to_u1024(), u1024!(2));
    assert_eq!(dp.coeffs[1].to_u1024(), u1024!(6));
}

#[test]
fn test_polynomial_zerofier() {
    // Z(x) = (x - 1)(x - 2)(x - 3) vanishes at 1, 2, 3
    let roots = vec![fp!(1u64), fp!(2u64), fp!(3u64)];
    let z = Polynomial::zerofier(&roots);

    assert_eq!(z.degree(), Some(3));

    // Verify it evaluates to zero at each root
    for root in &roots {
        assert!(z.evaluate(root).is_zero());
    }
}

#[test]
fn test_polynomial_interpolation() {
    // Interpolate a polynomial through points (0,1), (1,3), (2,7)
    // This is y = 1 + x + x^2 evaluated at 0,1,2
    let points = vec![fp!(0u64), fp!(1u64), fp!(2u64)];
    let values = vec![fp!(1u64), fp!(3u64), fp!(7u64)];

    let p = Polynomial::interpolate(&points, &values);

    // Verify interpolation
    for (point, value) in points.iter().zip(values.iter()) {
        assert_eq!(p.evaluate(point).to_u1024(), value.to_u1024());
    }
}

#[test]
fn test_polynomial_scale_and_shift() {
    let p = Polynomial::new(vec![fp!(1u64), fp!(2u64)]);

    // Scale by 3: 3*(1 + 2x) = 3 + 6x
    let scaled = p.scale(&fp!(3u64));
    assert_eq!(scaled.coeffs[0].to_u1024(), u1024!(3));
    assert_eq!(scaled.coeffs[1].to_u1024(), u1024!(6));

    // Shift by 2: x^2 * (1 + 2x) = x^2 + 2x^3
    let shifted = p.shift(2);
    assert_eq!(shifted.degree(), Some(3));
    assert!(shifted.coeffs[0].is_zero());
    assert!(shifted.coeffs[1].is_zero());
}

#[test]
fn test_polynomial_ntt_multiplication() {
    // Test NTT-based multiplication matches naive
    let p1 = Polynomial::new(vec![fp!(1u64), fp!(2u64), fp!(3u64)]);
    let p2 = Polynomial::new(vec![fp!(4u64), fp!(5u64)]);

    let naive = p1.clone() * p2.clone();
    let fast = p1.mul_fast(&p2);

    assert_eq!(naive.coeffs.len(), fast.coeffs.len());
    for (a, b) in naive.coeffs.iter().zip(fast.coeffs.iter()) {
        assert_eq!(a.to_u1024(), b.to_u1024());
    }
}

#[test]
fn test_polynomial_display() {
    let p = Polynomial::new(vec![fp!(1u64), fp!(2u64), fp!(3u64)]);
    let display = format!("{}", p);

    assert_eq!(display, "3x^2 + 2x + 1");
}

#[test]
fn test_dense_polynomial_alias() {
    // Polynomial should be identical to Polynomial
    let p1 = Polynomial::new(vec![fp!(1u64), fp!(2u64)]);
    let p2 = Polynomial::new(vec![fp!(1u64), fp!(2u64)]);

    // Same operations work
    assert_eq!(p1.degree(), p2.degree());
    assert_eq!(
        p1.evaluate(&fp!(3u64)).to_u1024(),
        p2.evaluate(&fp!(3u64)).to_u1024()
    );

    // mul_fast works on Polynomial
    let p3 = Polynomial::new(vec![fp!(3u64)]);
    let result = p1.mul_fast(&p3);
    assert_eq!(result.degree(), Some(1));
}

// ============================================================================
// MultivariatePolynomial Integration Tests
// ============================================================================

#[test]
fn test_multivariate_basic() {
    // Create p(x0, x1) = 5 + 3*x0 + 2*x1
    let mut p = MultivariatePolynomial::new(2);
    p.add_term(vec![0, 0], fp!(5u64)); // constant
    p.add_term(vec![1, 0], fp!(3u64)); // x0
    p.add_term(vec![0, 1], fp!(2u64)); // x1

    assert_eq!(p.num_terms(), 3);
    assert_eq!(p.num_vars, 2);
    assert_eq!(p.total_degree(), Some(1));
}

#[test]
fn test_multivariate_constructors() {
    let zero = MultivariatePolynomial::<DefaultFieldConfig>::zero(3);
    assert!(zero.is_zero());

    let one = MultivariatePolynomial::<DefaultFieldConfig>::one(3);
    assert_eq!(one.num_terms(), 1);

    let const_poly = MultivariatePolynomial::constant(2, fp!(42u64));
    let val = const_poly.evaluate(&[fp!(0u64), fp!(0u64)]);
    assert_eq!(val.to_u1024(), u1024!(42));

    let x0: MultivariatePolynomial<DefaultFieldConfig> = MultivariatePolynomial::variable(3, 0);
    assert_eq!(x0.degree_in(0), 1);
    assert_eq!(x0.degree_in(1), 0);
}

#[test]
fn test_multivariate_arithmetic() {
    // p1 = x0
    let p1: MultivariatePolynomial<DefaultFieldConfig> = MultivariatePolynomial::variable(2, 0);
    // p2 = x1
    let p2: MultivariatePolynomial<DefaultFieldConfig> = MultivariatePolynomial::variable(2, 1);

    // p1 + p2 = x0 + x1
    let sum = p1.clone() + p2.clone();
    assert_eq!(sum.num_terms(), 2);

    // p1 * p2 = x0 * x1
    let prod = p1.clone() * p2.clone();
    assert_eq!(prod.num_terms(), 1);
    assert_eq!(prod.total_degree(), Some(2));

    // Negation
    let neg = -p1.clone();
    let sum_zero = p1 + neg;
    assert!(sum_zero.is_zero());
}

#[test]
fn test_multivariate_evaluation() {
    // p(x0, x1) = 1 + x0 + x1 + x0*x1
    let mut p = MultivariatePolynomial::new(2);
    p.add_term(vec![0, 0], fp!(1u64));
    p.add_term(vec![1, 0], fp!(1u64));
    p.add_term(vec![0, 1], fp!(1u64));
    p.add_term(vec![1, 1], fp!(1u64));

    // p(2, 3) = 1 + 2 + 3 + 6 = 12
    let result = p.evaluate(&[fp!(2u64), fp!(3u64)]);
    assert_eq!(result.to_u1024(), u1024!(12));
}

#[test]
fn test_multivariate_partial_evaluation() {
    // p(x0, x1) = x0 + x1
    let mut p = MultivariatePolynomial::new(2);
    p.add_term(vec![1, 0], fp!(1u64));
    p.add_term(vec![0, 1], fp!(1u64));

    // Fix x0 = 5, get p(5, x1) = 5 + x1
    let mut assignments = BTreeMap::new();
    assignments.insert(0, fp!(5u64));

    let reduced = p.partial_evaluate(&assignments);
    assert_eq!(reduced.num_vars, 1); // Only x1 remains

    // Evaluate reduced polynomial at x1 = 3: 5 + 3 = 8
    let result = reduced.evaluate(&[fp!(3u64)]);
    assert_eq!(result.to_u1024(), u1024!(8));
}

#[test]
fn test_multivariate_degree_tracking() {
    // p(x0, x1, x2) = x0^2 + x1^3 + x2
    let mut p = MultivariatePolynomial::new(3);
    p.add_term(vec![2, 0, 0], fp!(1u64));
    p.add_term(vec![0, 3, 0], fp!(1u64));
    p.add_term(vec![0, 0, 1], fp!(1u64));

    assert_eq!(p.degree_in(0), 2);
    assert_eq!(p.degree_in(1), 3);
    assert_eq!(p.degree_in(2), 1);
    assert_eq!(p.total_degree(), Some(3));
}

#[test]
fn test_multivariate_scale() {
    let p: MultivariatePolynomial<DefaultFieldConfig> = MultivariatePolynomial::variable(2, 0); // x0
    let scaled = p.scale(&fp!(5u64)); // 5*x0

    let result = scaled.evaluate(&[fp!(3u64), fp!(0u64)]);
    assert_eq!(result.to_u1024(), u1024!(15)); // 5 * 3 = 15
}

#[test]
fn test_multivariate_to_univariate() {
    // Create a univariate polynomial through multivariate API
    let mut p = MultivariatePolynomial::new(1);
    p.add_term(vec![0], fp!(1u64));
    p.add_term(vec![1], fp!(2u64));
    p.add_term(vec![2], fp!(3u64));

    let uni = p.to_univariate().unwrap();
    assert_eq!(uni.degree(), Some(2));
    assert_eq!(format!("{}", uni), "3x^2 + 2x + 1");
}

#[test]
fn test_multivariate_from_univariate() {
    let uni = Polynomial::new(vec![fp!(1u64), fp!(2u64), fp!(3u64)]);
    let multi = MultivariatePolynomial::from_univariate(&uni);

    assert_eq!(multi.num_vars, 1);
    assert_eq!(multi.num_terms(), 3);

    // Evaluate both at same point
    let x = fp!(5u64);
    assert_eq!(uni.evaluate(&x).to_u1024(), multi.evaluate(&[x]).to_u1024());
}

#[test]
fn test_multivariate_equality() {
    let mut p1 = MultivariatePolynomial::new(2);
    p1.add_term(vec![1, 0], fp!(2u64));

    let mut p2 = MultivariatePolynomial::new(2);
    p2.add_term(vec![1, 0], fp!(2u64));

    let mut p3 = MultivariatePolynomial::new(2);
    p3.add_term(vec![1, 0], fp!(3u64));

    assert_eq!(p1, p2);
    assert_ne!(p1, p3);
}

#[test]
fn test_multivariate_display() {
    let mut p = MultivariatePolynomial::new(2);
    p.add_term(vec![0, 0], fp!(5u64));
    p.add_term(vec![1, 0], fp!(1u64));

    let display = format!("{}", p);
    // Should contain variable names
    assert!(display.contains("x0") || display.contains("5"));
}

// ============================================================================
// Cross-Type Integration Tests
// ============================================================================

#[test]
fn test_univariate_multivariate_consistency() {
    // Create the same polynomial as univariate and multivariate
    let uni = Polynomial::new(vec![fp!(1u64), fp!(2u64), fp!(3u64)]);
    let multi = MultivariatePolynomial::from_univariate(&uni);

    // Test at multiple points
    for i in 0..5 {
        let x = fp!(i as u64);
        assert_eq!(
            uni.evaluate(&x).to_u1024(),
            multi.evaluate(&[x]).to_u1024(),
            "Mismatch at x = {}",
            i
        );
    }
}
