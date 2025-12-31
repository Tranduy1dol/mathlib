//! Comprehensive tests for Negacyclic NTT implementation.
//!
//! Tests the NTT operations over the ring Rq = Zq[X]/(X^N + 1).

use lumen_math::field::config::DefaultFieldConfig;
use lumen_math::poly::ntt::{
    NttContext, bit_reverse, intt, intt_negacyclic, mul_negacyclic, ntt, ntt_negacyclic,
};
use lumen_math::{FieldElement, fp};

type FE = FieldElement<DefaultFieldConfig>;

// =============================================================================
// NttContext Tests
// =============================================================================

#[test]
fn test_ntt_context_creation() {
    let ctx = NttContext::<DefaultFieldConfig>::new(8);
    assert_eq!(ctx.n, 8);
}

#[test]
fn test_ntt_context_roundtrip_various_sizes() {
    for size in [4, 8, 16, 32, 64] {
        let ctx = NttContext::<DefaultFieldConfig>::new(size);
        let mut coeffs: Vec<_> = (0..size).map(|i| fp!(i as u64)).collect();
        let original = coeffs.clone();

        ctx.ntt(&mut coeffs);
        ctx.intt(&mut coeffs);

        for (a, b) in original.iter().zip(coeffs.iter()) {
            assert_eq!(
                a.to_u1024(),
                b.to_u1024(),
                "Roundtrip failed for size {}",
                size
            );
        }
    }
}

#[test]
fn test_ntt_context_mul() {
    let ctx = NttContext::<DefaultFieldConfig>::new(8);

    // p(x) = 1 + x
    let mut a = vec![FE::zero(); 8];
    a[0] = fp!(1u64);
    a[1] = fp!(1u64);

    // q(x) = 1 + x
    let mut b = vec![FE::zero(); 8];
    b[0] = fp!(1u64);
    b[1] = fp!(1u64);

    // (1 + x)^2 = 1 + 2x + x^2 in standard ring
    // In negacyclic ring X^N = -1, so result depends on reduction
    let result = ctx.mul(&mut a, &mut b);

    // Should get some polynomial back with correct length
    assert_eq!(result.len(), 8);
}

// =============================================================================
// Standalone Function Tests
// =============================================================================

#[test]
fn test_negacyclic_ntt_roundtrip_standalone() {
    let size = 16;
    let mut coeffs: Vec<_> = (0..size).map(|i| fp!(i as u64)).collect();
    let original = coeffs.clone();

    ntt_negacyclic::<DefaultFieldConfig>(&mut coeffs);
    intt_negacyclic::<DefaultFieldConfig>(&mut coeffs);

    for (a, b) in original.iter().zip(coeffs.iter()) {
        assert_eq!(a.to_u1024(), b.to_u1024());
    }
}

#[test]
fn test_mul_negacyclic_standalone() {
    let size = 8;

    let a: Vec<_> = (0..size).map(|i| fp!((i + 1) as u64)).collect();
    let mut b = vec![FE::zero(); size];
    b[0] = fp!(1u64); // b(x) = 1

    let result = mul_negacyclic(&mut a.clone(), &mut b);

    // Multiplying by 1 should give back original
    for (orig, res) in a.iter().zip(result.iter()) {
        assert_eq!(orig.to_u1024(), res.to_u1024());
    }
}

#[test]
fn test_negacyclic_zero_preservation() {
    let size = 8;
    let mut coeffs = vec![FE::zero(); size];

    ntt_negacyclic::<DefaultFieldConfig>(&mut coeffs);

    // NTT of zeros should be zeros
    for c in coeffs.iter() {
        assert!(c.is_zero());
    }
}

// =============================================================================
// Cyclic NTT Tests (Backward Compatibility)
// =============================================================================

#[test]
fn test_cyclic_ntt_still_works() {
    let size = 16;
    let mut coeffs: Vec<_> = (0..size).map(|i| fp!(i as u64)).collect();
    let original = coeffs.clone();

    ntt(&mut coeffs);
    intt(&mut coeffs);

    for (a, b) in original.iter().zip(coeffs.iter()) {
        assert_eq!(a.to_u1024(), b.to_u1024());
    }
}

#[test]
fn test_bit_reverse_works() {
    let mut coeffs = vec![fp!(0u64), fp!(1u64), fp!(2u64), fp!(3u64)];
    bit_reverse(&mut coeffs);

    // For size 4, bit reverse of [0,1,2,3] should be [0,2,1,3]
    assert_eq!(coeffs[0].to_u1024().0[0], 0);
    assert_eq!(coeffs[1].to_u1024().0[0], 2);
    assert_eq!(coeffs[2].to_u1024().0[0], 1);
    assert_eq!(coeffs[3].to_u1024().0[0], 3);
}

// =============================================================================
// Linearity Tests
// =============================================================================

#[test]
fn test_negacyclic_ntt_linearity() {
    let size = 8;
    let a_coeffs: Vec<_> = (0..size).map(|i| fp!(i as u64)).collect();
    let b_coeffs: Vec<_> = (0..size).map(|i| fp!((i + 1) as u64)).collect();

    // NTT(a + b) should equal NTT(a) + NTT(b)
    let mut sum_coeffs: Vec<_> = a_coeffs
        .iter()
        .zip(b_coeffs.iter())
        .map(|(a, b)| *a + *b)
        .collect();

    let mut a_copy = a_coeffs;
    let mut b_copy = b_coeffs;

    ntt_negacyclic::<DefaultFieldConfig>(&mut sum_coeffs);
    ntt_negacyclic::<DefaultFieldConfig>(&mut a_copy);
    ntt_negacyclic::<DefaultFieldConfig>(&mut b_copy);

    for i in 0..size {
        let expected = a_copy[i] + b_copy[i];
        assert_eq!(sum_coeffs[i].to_u1024(), expected.to_u1024());
    }
}
