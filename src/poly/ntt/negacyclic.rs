//! Negacyclic NTT (Number Theoretic Transform) over Zq[X]/(X^N + 1).
//!
//! This module provides negacyclic NTT for polynomial multiplication in the ring
//! Rq = Zq[X]/(X^N + 1), which is essential for lattice-based cryptography
//! schemes like Kyber and Dilithium.
//!
//! # Mathematical Background
//!
//! The negacyclic NTT differs from the standard cyclic NTT by using a primitive
//! 2Nth root of unity ψ where ψ^N ≡ -1 (mod q), rather than an Nth root of unity.
//!
//! The transform involves:
//! 1. Pre-multiply coefficients by powers of ψ (the "twist")
//! 2. Apply standard NTT with ω = ψ^2 (Nth root of unity)
//!
//! The inverse involves:
//! 1. Apply inverse NTT
//! 2. Post-multiply by inverse powers of ψ and scale by n^-1

use crate::{FieldConfig, FieldElement, U1024};

use super::cyclic::bit_reverse;

/// Performs Negacyclic NTT on the input coefficients.
///
/// Computes the NTT over Zq[X]/(X^N+1) using Cooley-Tukey algorithm.
/// This is the forward transform for lattice-based cryptography (Kyber/Dilithium).
///
/// # Panics
/// Panics if the coefficient length is not a power of two.
pub fn ntt_negacyclic<C: FieldConfig>(coeffs: &mut [FieldElement<C>]) {
    let n = coeffs.len();
    assert!(n.is_power_of_two(), "NTT size must be power of two");

    // Step 1: Pre-multiply by powers of ψ (twist)
    let psi = FieldElement::<C>::new(C::PRIMITIVE_2NTH_ROOT);
    let mut psi_power = FieldElement::<C>::one();
    for coeff in coeffs.iter_mut() {
        *coeff = *coeff * psi_power;
        psi_power = psi_power * psi;
    }

    // Step 2: Apply standard NTT (Cooley-Tukey, in-place)
    bit_reverse(coeffs);

    let mut len = 2;
    while len <= n {
        let half_len = len / 2;

        // Compute ω for current layer
        // ω = ψ^2 is the primitive Nth root of unity
        let log_len = len.trailing_zeros();
        let factor = 32 - log_len;

        let omega_base = FieldElement::<C>::new(C::PRIMITIVE_2NTH_ROOT);
        let mut w_len = omega_base * omega_base; // ψ^2 = ω (Nth root)
        for _ in 0..factor {
            w_len = w_len * w_len;
        }

        for i in (0..n).step_by(len) {
            let mut w = FieldElement::<C>::one();
            for j in 0..half_len {
                let u = coeffs[i + j];
                let v = coeffs[i + j + half_len] * w;
                coeffs[i + j] = u + v;
                coeffs[i + j + half_len] = u - v;
                w = w * w_len;
            }
        }
        len <<= 1;
    }
}

/// Performs Inverse Negacyclic NTT on the input coefficients.
///
/// Recovers polynomial coefficients from NTT representation over Zq[X]/(X^N+1).
/// Uses Gentleman-Sande algorithm for the inverse transform.
///
/// # Panics
/// Panics if the coefficient length is not a power of two.
pub fn intt_negacyclic<C: FieldConfig>(coeffs: &mut [FieldElement<C>]) {
    let n = coeffs.len();
    assert!(n.is_power_of_two(), "INTT size must be power of two");

    // Step 1: Apply Gentleman-Sande inverse NTT
    let mut len = n;
    while len >= 2 {
        let half_len = len / 2;

        let log_len = len.trailing_zeros();
        let factor = 32 - log_len;

        let omega_base = FieldElement::<C>::new(C::PRIMITIVE_2NTH_ROOT);
        let omega = omega_base * omega_base;
        let mut w_len_inv = omega.inv();
        for _ in 0..factor {
            w_len_inv = w_len_inv * w_len_inv;
        }

        for i in (0..n).step_by(len) {
            let mut w = FieldElement::<C>::one();
            for j in 0..half_len {
                let u = coeffs[i + j];
                let v = coeffs[i + j + half_len];
                coeffs[i + j] = u + v;
                coeffs[i + j + half_len] = (u - v) * w;
                w = w * w_len_inv;
            }
        }
        len >>= 1;
    }

    bit_reverse(coeffs);

    // Step 2: Post-multiply by inverse powers of ψ and scale by n^-1
    let psi = FieldElement::<C>::new(C::PRIMITIVE_2NTH_ROOT);
    let psi_inv = psi.inv();
    let n_inv = FieldElement::<C>::new(U1024::from_u64(n as u64)).inv();

    let mut psi_inv_power = FieldElement::<C>::one();
    for coeff in coeffs.iter_mut() {
        *coeff = *coeff * psi_inv_power * n_inv;
        psi_inv_power = psi_inv_power * psi_inv;
    }
}

/// Multiplies two polynomials in Rq = Zq[X]/(X^N+1) using Negacyclic NTT.
///
/// The result is automatically reduced modulo (X^N+1).
///
/// # Arguments
/// * `a` - First polynomial coefficients (will be transformed in-place)
/// * `b` - Second polynomial coefficients (will be transformed in-place)
///
/// # Returns
/// The product polynomial coefficients.
///
/// # Panics
/// Panics if `a` and `b` have different lengths or lengths are not powers of two.
pub fn mul_negacyclic<C: FieldConfig>(
    a: &mut [FieldElement<C>],
    b: &mut [FieldElement<C>],
) -> Vec<FieldElement<C>> {
    let n = a.len();
    assert_eq!(n, b.len(), "Polynomials must have same length");

    ntt_negacyclic(a);
    ntt_negacyclic(b);

    let mut result: Vec<_> = a.iter().zip(b.iter()).map(|(x, y)| *x * *y).collect();

    intt_negacyclic(&mut result);
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::config::DefaultFieldConfig;
    use crate::fp;

    #[test]
    fn test_negacyclic_ntt_roundtrip() {
        let size = 8;
        let mut coeffs: Vec<_> = (0..size).map(|i| fp!(i as u64)).collect();
        let original = coeffs.clone();

        ntt_negacyclic::<DefaultFieldConfig>(&mut coeffs);
        intt_negacyclic::<DefaultFieldConfig>(&mut coeffs);

        for (a, b) in original.iter().zip(coeffs.iter()) {
            assert_eq!(a.to_u1024(), b.to_u1024());
        }
    }

    #[test]
    fn test_negacyclic_ntt_zero_polynomial() {
        let size = 8;
        let mut coeffs = vec![FieldElement::<DefaultFieldConfig>::zero(); size];

        ntt_negacyclic(&mut coeffs);

        for c in coeffs.iter() {
            assert!(c.is_zero());
        }
    }

    #[test]
    #[should_panic(expected = "NTT size must be power of two")]
    fn test_negacyclic_ntt_non_power_of_two() {
        let mut coeffs = vec![fp!(1u64), fp!(2u64), fp!(3u64)]; // Size 3
        ntt_negacyclic::<DefaultFieldConfig>(&mut coeffs);
    }
}
