//! Number Theoretic Transform (NTT) module for polynomial operations.
//!
//! This module provides NTT implementations for fast polynomial multiplication:
//!
//! - **Cyclic NTT**: Standard NTT over Zq[X]/(X^N - 1)
//! - **Negacyclic NTT**: NTT over Zq[X]/(X^N + 1) for lattice-based crypto
//!
//! # Small-Modulus Field Types (Recommended for Production)
//!
//! For Kyber and Dilithium, use the optimized small-field types in [`small`]:
//!
//! ```rust,ignore
//! use lumen_math::poly::ntt::small::{KyberFieldElement, DilithiumFieldElement};
//!
//! // Efficient native arithmetic with Barrett reduction
//! let a = KyberFieldElement::new(100);
//! let b = KyberFieldElement::new(200);
//! let c = a * b;  // Uses u16 arithmetic, not U1024!
//! ```
//!
//! # Generic NTT (for large moduli)
//!
//! For large moduli (>64 bits), use the generic `FieldConfig`-based NTT:
//!
//! ```rust,ignore
//! use lumen_math::poly::ntt::{ntt, intt, NttContext};
//! use lumen_math::DefaultFieldConfig;
//!
//! ntt::<DefaultFieldConfig>(&mut coeffs);
//! intt::<DefaultFieldConfig>(&mut coeffs);
//! ```

pub mod config;
pub mod cyclic;
pub mod negacyclic;
pub mod small;

// Re-export cyclic NTT functions for backward compatibility
pub use cyclic::{bit_reverse, intt, ntt};

// Re-export negacyclic NTT functions
pub use negacyclic::{intt_negacyclic, mul_negacyclic, ntt_negacyclic};

// Re-export lattice field configs (deprecated, use small module instead)
#[allow(deprecated)]
pub use config::{DilithiumFieldConfig, KyberFieldConfig};

use crate::{FieldConfig, FieldElement, U1024};
use std::marker::PhantomData;

/// Context for NTT operations, encapsulating precomputed values.
///
/// This struct provides a clean API for performing NTT operations
/// and caches precomputed powers of ψ for efficiency.
///
/// # Type Parameters
/// * `C` - Field configuration (e.g., `KyberFieldConfig`, `DilithiumFieldConfig`)
///
/// # Example
/// ```rust,ignore
/// use lumen_math::poly::ntt::{NttContext, KyberFieldConfig};
///
/// let ctx = NttContext::<KyberFieldConfig>::new(256);
/// let mut coeffs = vec![FieldElement::zero(); 256];
/// ctx.ntt(&mut coeffs);
/// ctx.intt(&mut coeffs);
/// ```
pub struct NttContext<C: FieldConfig> {
    /// Polynomial ring degree (must be power of 2)
    pub n: usize,
    /// Precomputed powers of ψ: [ψ^0, ψ^1, ..., ψ^(n-1)]
    psi_powers: Vec<FieldElement<C>>,
    /// Precomputed powers of ψ^-1 for inverse transform
    psi_inv_powers: Vec<FieldElement<C>>,
    /// Precomputed n^-1 for inverse scaling
    n_inv: FieldElement<C>,
    /// Phantom data for field config
    _marker: PhantomData<C>,
}

impl<C: FieldConfig> NttContext<C> {
    /// Creates a new NTT context for polynomials of degree n.
    ///
    /// # Panics
    /// Panics if `n` is not a power of two.
    pub fn new(n: usize) -> Self {
        assert!(n.is_power_of_two(), "NTT degree must be power of two");

        let psi = FieldElement::<C>::new(C::PRIMITIVE_2NTH_ROOT);
        let psi_inv = psi.inv();
        let n_inv = FieldElement::<C>::new(U1024::from_u64(n as u64)).inv();

        // Precompute ψ powers
        let mut psi_powers = Vec::with_capacity(n);
        let mut current = FieldElement::<C>::one();
        for _ in 0..n {
            psi_powers.push(current);
            current = current * psi;
        }

        // Precompute ψ^-1 powers
        let mut psi_inv_powers = Vec::with_capacity(n);
        current = FieldElement::<C>::one();
        for _ in 0..n {
            psi_inv_powers.push(current);
            current = current * psi_inv;
        }

        Self {
            n,
            psi_powers,
            psi_inv_powers,
            n_inv,
            _marker: PhantomData,
        }
    }

    /// Forward negacyclic NTT using precomputed values.
    ///
    /// # Panics
    /// Panics if `coeffs.len() != self.n`.
    pub fn ntt(&self, coeffs: &mut [FieldElement<C>]) {
        assert_eq!(
            coeffs.len(),
            self.n,
            "Coefficient length must match context size"
        );

        // Step 1: Pre-multiply by precomputed powers of ψ
        for (i, coeff) in coeffs.iter_mut().enumerate() {
            *coeff = *coeff * self.psi_powers[i];
        }

        // Step 2: Apply standard NTT
        bit_reverse(coeffs);

        let mut len = 2;
        while len <= self.n {
            let half_len = len / 2;

            // Compute twiddle factor ω^(n/len) for this layer.
            // Starting from ω = ψ² (Nth root), we square it (log2(n) - log2(len)) times.
            let log_n = (self.n as u32).trailing_zeros();
            let log_len = len.trailing_zeros();
            let factor = log_n - log_len;

            // ω = ψ^2, then raised to appropriate power for this layer
            let omega_base = FieldElement::<C>::new(C::PRIMITIVE_2NTH_ROOT);
            let mut w_len = omega_base * omega_base;
            for _ in 0..factor {
                w_len = w_len * w_len;
            }

            for i in (0..self.n).step_by(len) {
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

    /// Inverse negacyclic NTT using precomputed values.
    ///
    /// # Panics
    /// Panics if `coeffs.len() != self.n`.
    pub fn intt(&self, coeffs: &mut [FieldElement<C>]) {
        assert_eq!(
            coeffs.len(),
            self.n,
            "Coefficient length must match context size"
        );

        // Step 1: Apply Gentleman-Sande inverse NTT
        let mut len = self.n;
        while len >= 2 {
            let half_len = len / 2;

            // Compute inverse twiddle factor ω^(-n/len) for this layer.
            let log_n = (self.n as u32).trailing_zeros();
            let log_len = len.trailing_zeros();
            let factor = log_n - log_len;

            let omega_base = FieldElement::<C>::new(C::PRIMITIVE_2NTH_ROOT);
            let omega = omega_base * omega_base;
            let mut w_len_inv = omega.inv();
            for _ in 0..factor {
                w_len_inv = w_len_inv * w_len_inv;
            }

            for i in (0..self.n).step_by(len) {
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

        // Step 2: Post-multiply by precomputed powers of ψ^-1 and scale
        for (i, coeff) in coeffs.iter_mut().enumerate() {
            *coeff = *coeff * self.psi_inv_powers[i] * self.n_inv;
        }
    }

    /// Polynomial multiplication in Rq = Zq[X]/(X^N+1).
    ///
    /// This function does not mutate its inputs. It clones both polynomials
    /// internally, transforms them via NTT, performs pointwise multiplication,
    /// and returns the inverse-transformed result.
    ///
    /// # Arguments
    /// * `a` - First polynomial coefficients
    /// * `b` - Second polynomial coefficients
    ///
    /// # Returns
    /// The product polynomial coefficients in Rq.
    ///
    /// # Panics
    /// Panics if `a.len() != self.n` or `b.len() != self.n`.
    pub fn mul(&self, a: &[FieldElement<C>], b: &[FieldElement<C>]) -> Vec<FieldElement<C>> {
        assert_eq!(
            a.len(),
            self.n,
            "First polynomial length must match context size"
        );
        assert_eq!(
            b.len(),
            self.n,
            "Second polynomial length must match context size"
        );

        // Clone inputs to avoid mutation
        let mut a_ntt = a.to_vec();
        let mut b_ntt = b.to_vec();

        self.ntt(&mut a_ntt);
        self.ntt(&mut b_ntt);

        let mut result: Vec<_> = a_ntt
            .iter()
            .zip(b_ntt.iter())
            .map(|(x, y)| *x * *y)
            .collect();

        self.intt(&mut result);
        result
    }

    /// Polynomial multiplication with mutable inputs (in-place NTT).
    ///
    /// This is a more efficient variant that transforms the inputs in-place.
    /// After calling this function, `a` and `b` will contain their NTT representations.
    ///
    /// # Warning
    /// This function mutates both `a` and `b` by applying the forward NTT.
    /// If you need to preserve the original coefficients, use [`mul`] instead.
    ///
    /// # Panics
    /// Panics if `a.len() != self.n` or `b.len() != self.n`.
    pub fn mul_in_place(
        &self,
        a: &mut [FieldElement<C>],
        b: &mut [FieldElement<C>],
    ) -> Vec<FieldElement<C>> {
        assert_eq!(
            a.len(),
            self.n,
            "First polynomial length must match context size"
        );
        assert_eq!(
            b.len(),
            self.n,
            "Second polynomial length must match context size"
        );

        self.ntt(a);
        self.ntt(b);

        let mut result: Vec<_> = a.iter().zip(b.iter()).map(|(x, y)| *x * *y).collect();

        self.intt(&mut result);
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::config::DefaultFieldConfig;
    use crate::fp;

    #[test]
    fn test_ntt_context_roundtrip() {
        let ctx = NttContext::<DefaultFieldConfig>::new(8);
        let mut coeffs: Vec<_> = (0..8).map(|i| fp!(i as u64)).collect();
        let original = coeffs.clone();

        ctx.ntt(&mut coeffs);
        ctx.intt(&mut coeffs);

        for (a, b) in original.iter().zip(coeffs.iter()) {
            assert_eq!(a.to_u1024(), b.to_u1024());
        }
    }

    #[test]
    fn test_ntt_context_zero() {
        let ctx = NttContext::<DefaultFieldConfig>::new(8);
        let mut coeffs = vec![FieldElement::<DefaultFieldConfig>::zero(); 8];

        ctx.ntt(&mut coeffs);

        for c in coeffs.iter() {
            assert!(c.is_zero());
        }
    }

    #[test]
    #[should_panic(expected = "NTT degree must be power of two")]
    fn test_ntt_context_invalid_size() {
        let _ctx = NttContext::<DefaultFieldConfig>::new(7);
    }
}
