use crate::U1024;
use crate::traits::BigInt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MontgomeryParams {
    pub modulus: U1024,
    pub r2: U1024,
    pub n_prime: U1024,
}

impl MontgomeryParams {
    pub fn new(modulus: U1024) -> Self {
        let n_prime = Self::compute_n_prime(&modulus);
        let r2 = Self::compute_r2(&modulus);

        Self {
            modulus,
            r2,
            n_prime,
        }
    }

    fn compute_n_prime(modulus: &U1024) -> U1024 {
        let mut inv = 1u64;
        let p0 = modulus.0[0];

        for _ in 0..6 {
            inv = inv.wrapping_mul(2u64.wrapping_sub(p0.wrapping_mul(inv)));
        }

        let mut inv_big = U1024::from_u64(inv);

        let two = U1024::from_u64(2);

        for _ in 0..4 {
            let term = *modulus * inv_big;

            let (correction, _) = two.borrowing_sub(&term);

            inv_big = inv_big * correction;
        }

        let (neg_inv, _) = U1024::zero().borrowing_sub(&inv_big);
        neg_inv
    }

    fn compute_r2(modulus: &U1024) -> U1024 {
        let mut acc = U1024::one();

        for _ in 0..2048 {
            let (acc_shifted, carry) = acc.carrying_add(&acc);
            let (sub_res, borrow) = acc_shifted.borrowing_sub(modulus);

            if carry || !borrow {
                acc = sub_res;
            } else {
                acc = acc_shifted;
            }
        }

        acc
    }

    #[inline]
    pub fn reduce(&self, lo: &U1024, hi: &U1024) -> U1024 {
        let m = (*lo) * self.n_prime;
        let (mn_lo, mn_hi) = m.full_mul(&self.modulus);

        let (_, carry_lo) = lo.carrying_add(&mn_lo);
        let (res_hi, carry_hi) = hi.carrying_add(&mn_hi);
        let (t, carry_final) = if carry_lo {
            res_hi.carrying_add(&U1024::one())
        } else {
            (res_hi, false)
        };

        if carry_hi || carry_final {
            let (sub_res, _) = t.borrowing_sub(&self.modulus);
            return sub_res;
        }

        let (sub_res, borrow) = t.borrowing_sub(&self.modulus);
        if !borrow { sub_res } else { t }
    }
}
