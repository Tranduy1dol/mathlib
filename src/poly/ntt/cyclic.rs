//! Cyclic NTT (Number Theoretic Transform) over Zq[X]/(X^N - 1).
//!
//! This module provides the standard cyclic NTT for polynomial multiplication
//! in the ring Zq[X]/(X^N - 1).

use crate::{FieldConfig, FieldElement, U1024};

/// Reorders coefficients in bit-reversal permutation order.
pub fn bit_reverse<C: FieldConfig>(coeffs: &mut [FieldElement<C>]) {
    let n = coeffs.len();
    let leading_zeros = n.leading_zeros() + 1;

    for i in 0..n {
        let rev = i.reverse_bits() >> leading_zeros;
        if i < rev {
            coeffs.swap(i, rev);
        }
    }
}

/// Performs the Number Theoretic Transform (NTT) on the input coefficients.
pub fn ntt<C: FieldConfig>(coeffs: &mut [FieldElement<C>]) {
    let n = coeffs.len();
    assert!(n.is_power_of_two(), "NTT size must be power of two");

    bit_reverse(coeffs);

    let mut len = 2;
    while len <= n {
        let half_len = len / 2;

        // Compute twiddle factor ω^(2^32/len) for this layer.
        // ROOT_OF_UNITY is a primitive 2^32-th root of unity, so we square it
        // (32 - log2(len)) times to get the proper twiddle factor for length len.
        let log_len = len.trailing_zeros();
        let factor = 32 - log_len;

        let mut w_len = FieldElement::<C>::new(C::ROOT_OF_UNITY);
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

/// Performs the Inverse Number Theoretic Transform (INTT) on the input coefficients.
pub fn intt<C: FieldConfig>(coeffs: &mut [FieldElement<C>]) {
    let n = coeffs.len();

    ntt(coeffs);

    coeffs[1..].reverse();

    let n_val = U1024::from_u64(n as u64);
    let n_elem = FieldElement::<C>::new(n_val);
    let n_inv = n_elem.inv();

    for c in coeffs.iter_mut() {
        *c = *c * n_inv;
    }
}
