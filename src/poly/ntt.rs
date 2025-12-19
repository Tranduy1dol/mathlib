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

    // Use U1024::from_u64 directly if possible, or construct via array
    // U1024::from_u64 is available as inherent methods on U1024 if implemented or via macro?
    // u1024!(...) works but is it const? No need for const here.
    let n_val = U1024::from_u64(n as u64);
    let n_elem = FieldElement::<C>::new(n_val);
    let n_inv = n_elem.inv();

    for c in coeffs.iter_mut() {
        *c = *c * n_inv;
    }
}
