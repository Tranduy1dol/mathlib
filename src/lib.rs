//! Mathlib - A cryptographic mathematics library.
//!
//! This library provides fundamental building blocks for cryptographic applications:
//!
//! - **Big Integers**: `U1024` (unsigned) and `I1024` (signed) 1024-bit integers
//! - **Field Arithmetic**: `FieldElement` with Montgomery multiplication
//! - **Polynomials**: Univariate and multivariate polynomial operations
//! - **Protocols**: GCD, CRT, and other cryptographic protocols
//! - **Traits**: `BigInt`, `Digest` for common operations

pub mod big_int;
pub mod field;
pub mod poly;
pub mod protocol;
pub mod traits;

pub use lumen_math_macros::FieldConfig;

// Big integers
pub use crate::big_int::{I1024, U1024, backend::*};

// Field operations
pub use crate::field::{
    config::{DefaultFieldConfig, FieldConfig},
    element::FieldElement,
    montgomery::MontgomeryContext,
};

// Polynomials
pub use crate::poly::{multivariate::MultivariatePolynomial, ntt::*, univariate::Polynomial};

// Lattice-specific configs (Kyber/Dilithium)
pub use crate::poly::ntt::config::{DilithiumFieldConfig, KyberFieldConfig};

// Negacyclic NTT (explicit re-export for convenience)
pub use crate::poly::ntt::{NttContext, intt_negacyclic, mul_negacyclic, ntt_negacyclic};

// Traits
pub use traits::{BigInt, Digest};

/// Computes N' for Montgomery reduction where P * N' = -1 mod 2^1024.
///
/// This is a convenience re-export of `MontgomeryContext::compute_n_prime`.
pub fn compute_n_prime(modulus: &U1024) -> U1024 {
    MontgomeryContext::compute_n_prime(modulus)
}

/// Computes R^2 mod P where R = 2^1024.
///
/// This is a convenience re-export of `MontgomeryContext::compute_r2`.
pub fn compute_r2(modulus: &U1024) -> U1024 {
    MontgomeryContext::compute_r2(modulus)
}
