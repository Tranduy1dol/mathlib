use std::ops::{Add, Mul, Sub};

use crate::num::u256::U256;

#[repr(align(16))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct U128(pub [u64; 2]);

impl U128 {
    pub const ZERO: Self = Self([0; 2]);

    pub fn carrying_add(&self, rhs: &Self) -> (Self, bool) {
        let mut result = U128::ZERO;
        let mut carry: u64 = 0;

        for i in 0..2 {
            let (sum1, carry1) = self.0[i].overflowing_add(rhs.0[i]);
            let (sum2, carry2) = sum1.overflowing_add(carry);
            result.0[i] = sum2;
            carry = (carry1 as u64) + (carry2 as u64);
        }
        (result, carry != 0)
    }

    pub fn borrowing_sub(&self, rhs: &Self) -> (Self, bool) {
        let mut result = U128::ZERO;
        let mut borrow: u64 = 0;

        for i in 0..2 {
            let (diff1, borrow1) = self.0[i].overflowing_sub(rhs.0[i]);
            let (diff2, borrow2) = diff1.overflowing_sub(borrow);
            result.0[i] = diff2;
            borrow = (borrow1 as u64) + (borrow2 as u64);
        }
        (result, borrow != 0)
    }

    pub fn full_mul(&self, rhs: &Self) -> U256 {
        let mut result = U256([0; 4]);

        for i in 0..2 {
            let mut carry: u128 = 0;
            for j in 0..2 {
                let prod =
                    (self.0[i] as u128) * (rhs.0[j] as u128) + (result.0[i + j] as u128) + carry;

                result.0[i + j] = prod as u64;
                carry = prod >> 64;
            }
            result.0[i + 2] = result.0[i + 2].wrapping_add(carry as u64);
        }
        result
    }
}

impl Add for U128 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        self.carrying_add(&rhs).0
    }
}

impl Sub for U128 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        self.borrowing_sub(&rhs).0
    }
}

impl Mul for U128 {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        let full_result = self.full_mul(&rhs);
        U128([full_result.0[0], full_result.0[1]])
    }
}
