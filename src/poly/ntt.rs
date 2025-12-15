use crate::{FieldElement, get_params, u1024};

/// Reorders coefficients in bit-reversal permutation order.
///
/// This function permutes the input slice such that the element at index `i` is swapped
/// with the element at index `rev(i)`, where `rev(i)` is the bit-reversal of `i`
/// with respect to the slice length `n`. The length `n` must be a power of two.
pub fn bit_reverse(coeffs: &mut [FieldElement]) {
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
///
/// This function computes the NTT (which is a Discrete Fourier Transform over a finite field)
/// in-place using the Cooley-Tukey algorithm. The input length must be a power of two.
/// The transform maps the polynomial representation from coefficient form to evaluation form.
pub fn ntt(coeffs: &mut [FieldElement]) {
    let n = coeffs.len();
    assert!(n.is_power_of_two(), "NTT size must be power of two");

    let params = get_params();

    bit_reverse(coeffs);

    let mut len = 2;
    while len <= n {
        let half_len = len / 2;

        let log_len = len.trailing_zeros();
        let factor = 32 - log_len;

        let mut w_len = FieldElement::new(params.root_of_unity, params);
        for _ in 0..factor {
            w_len = w_len * w_len;
        }

        for i in (0..n).step_by(len) {
            let mut w = FieldElement::one(params);

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
///
/// This function computes the inverse NTT in-place. It first applies the forward NTT,
/// then reverses the order of the coefficients (skipping the first one), and finally
/// scales all coefficients by the modular inverse of the length `n`.
/// The transform maps the polynomial representation from evaluation form back to coefficient form.
pub fn intt(coeffs: &mut [FieldElement]) {
    let n = coeffs.len();

    ntt(coeffs);

    coeffs[1..].reverse();

    let params = coeffs[0].params;
    let n_val = u1024!(n as u64);
    let n_elem = FieldElement::new(n_val, params);
    let n_inv = n_elem.inv();

    for c in coeffs.iter_mut() {
        *c = *c * n_inv;
    }
}
