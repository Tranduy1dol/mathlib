//! Polynomial module providing univariate and multivariate polynomial arithmetic.
//!
//! This module provides:
//! - [`Polynomial`] - Univariate polynomial with comprehensive operations
//! - [`MultivariatePolynomial`] - Multivariate polynomial with sparse representation
//! - NTT-based fast polynomial multiplication

pub mod multivariate;
pub mod ntt;
pub mod univariate;

// Primary exports
pub use multivariate::MultivariatePolynomial;
pub use ntt::*;
pub use univariate::Polynomial;
