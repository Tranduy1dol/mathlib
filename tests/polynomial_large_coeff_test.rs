use mathlib::{DensePolynomial, fp};

#[test]
fn test_polynomial_display_small_coefficients() {
    // P(x) = 3x^2 + 2x + 1 (small coefficients fit in u64)
    let poly = DensePolynomial::new(vec![fp!(1u64), fp!(2u64), fp!(3u64)]);
    let display = format!("{}", poly);
    assert_eq!(display, "3x^2 + 2x + 1");
}

#[test]
fn test_polynomial_display_coefficient_one() {
    // Verify that coefficient 1 is properly detected
    let poly = DensePolynomial::new(vec![
        fp!(0u64),
        fp!(1u64), // This should display as just "x" not "1x"
    ]);

    let display = format!("{}", poly);
    assert_eq!(display, "x");
}

#[test]
fn test_polynomial_display_large_u64() {
    // Test with the maximum u64 value
    let poly = DensePolynomial::new(vec![fp!(u64::MAX), fp!(2u64)]);

    let display = format!("{}", poly);
    // Should still be in decimal since it fits in one limb
    assert!(display.contains(&u64::MAX.to_string()));
    assert!(!display.contains("0x")); // Should not use hex for single limb
}

#[test]
fn test_polynomial_display_format_consistency() {
    // Test various small coefficient sizes
    let test_cases = vec![
        (vec![fp!(0u64), fp!(1u64), fp!(1u64)], "x^2 + x"),
        (vec![fp!(5u64), fp!(0u64), fp!(1u64)], "x^2 + 5"),
        (vec![fp!(1u64), fp!(1u64), fp!(1u64)], "x^2 + x + 1"),
    ];

    for (coeffs, expected) in test_cases {
        let poly = DensePolynomial::new(coeffs);
        let display = format!("{}", poly);
        assert_eq!(display, expected, "Failed for polynomial: {}", display);
    }
}

#[test]
fn test_polynomial_display_zero_handling() {
    // Verify zero coefficients are skipped properly
    let poly = DensePolynomial::new(vec![fp!(7u64), fp!(0u64), fp!(0u64), fp!(5u64)]);

    let display = format!("{}", poly);
    assert_eq!(display, "5x^3 + 7");
}

#[test]
fn test_polynomial_mixed_sizes_realistic() {
    // Test with large numbers that actually occur in field operations
    // Using realistic field element values
    let coeffs = vec![fp!(12345u64), fp!(67890u64), fp!(999999u64)];

    let poly = DensePolynomial::new(coeffs);
    let display = format!("{}", poly);

    // All should be displayed in decimal
    assert!(display.contains("999999"));
    assert!(display.contains("67890"));
    assert!(display.contains("12345"));
}
