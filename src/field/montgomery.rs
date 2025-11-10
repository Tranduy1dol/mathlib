use std::ops::{Add, Mul, Sub};

use crate::num::{u256::U256, u512::U512};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MontgomeryModulus {
    pub p: U256,
    pub r2: U256,
    pub mod_inv: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FieldElement {
    inner: U256,
    modulus: MontgomeryModulus,
}

impl MontgomeryModulus {
    pub fn reduce(&self, t: &U512) -> U256 {
        let mut t = *t;
        for i in 0..4 {
            let m = t.0[i].wrapping_mul(self.mod_inv);
            let mut carry = 0_u128;
            for j in 0..4 {
                let product = (m as u128) * (self.p.0[j] as u128);
                let sum = (t.0[i + j] as u128) + product + carry;
                t.0[i + j] = sum as u64;
                carry = sum >> 64;
            }

            let mut k = i + 4;
            while carry > 0 && k < 8 {
                let sum = (t.0[k] as u128) + carry;
                t.0[k] = sum as u64;
                carry = sum >> 64;
                k += 1;
            }
        }

        let mut result = U256([t.0[4], t.0[5], t.0[6], t.0[7]]);
        if !result.borrowing_sub(&self.p).1 {
            result = result.wrapping_sub(&self.p);
        }
        result
    }
}

impl Add for FieldElement {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        debug_assert_eq!(self.modulus.p, rhs.modulus.p);
        let (sum, carry) = self.inner.carrying_add(&rhs.inner);
        let mut inner = sum;
        if carry || !inner.borrowing_sub(&self.modulus.p).1 {
            inner = inner.wrapping_sub(&self.modulus.p);
        }
        FieldElement {
            inner,
            modulus: self.modulus,
        }
    }
}

impl Sub for FieldElement {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        debug_assert_eq!(self.modulus.p, rhs.modulus.p);
        let (diff, borrow) = self.inner.borrowing_sub(&rhs.inner);
        let inner = if borrow {
            diff.wrapping_add(&self.modulus.p)
        } else {
            diff
        };
        FieldElement {
            inner,
            modulus: self.modulus,
        }
    }
}

impl Mul for FieldElement {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        debug_assert_eq!(self.modulus.p, rhs.modulus.p);
        let t = self.inner.full_mul(&rhs.inner);
        let result_inner = self.modulus.reduce(&t);
        FieldElement {
            inner: result_inner,
            modulus: self.modulus,
        }
    }
}
