use crate::field::constants::get_params;
use crate::field::element::FieldElement;

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
