pub mod big_int;
pub mod field;
pub mod poly;
pub mod traits;

pub use mathlib_macros::FieldConfig;

pub use crate::big_int::{backend::*, u1024::U1024};
pub use crate::field::{
    config::{DefaultFieldConfig, FieldConfig},
    element::FieldElement,
    montgomery::MontgomeryContext,
};
pub use crate::poly::{dense::DensePolynomial, ntt::*};

pub use traits::*;

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
