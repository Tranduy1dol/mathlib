use std::ops::{Add, BitXor, Mul, Sub};

use crate::num::u512::U512;

#[repr(align(32))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct U256(pub [u64; 4]);

impl U256 {
    pub fn full_mul(&self, rhs: &Self) -> U512 {
        let mut result = U512::ZERO;

        for i in 0..4 {
            let mut carry: u128 = 0;
            for j in 0..4 {
                let a_limb = self.0[i] as u128;
                let b_limb = rhs.0[j] as u128;

                let result_limb = result.0[i + j] as u128;

                let product = a_limb * b_limb + result_limb + carry;

                result.0[i + j] = product as u64;
                carry = product >> 64;
            }

            result.0[i + 4] += carry as u64;
        }

        result
    }

    pub fn xor_safe(&self, rhs: &Self) -> Self {
        let mut result = U256([0; 4]);
        for i in 0..4 {
            result.0[i] = self.0[i] ^ rhs.0[i];
        }
        result
    }

    pub fn carrying_add(&self, rhs: &Self) -> (Self, bool) {
        let mut result = U256([0; 4]);
        let mut carry = 0;

        for i in 0..4 {
            let (sum1, carry1) = self.0[i].overflowing_add(rhs.0[i]);
            let (sum2, carry2) = sum1.overflowing_add(carry);

            result.0[i] = sum2;
            carry = (carry1 as u64) + (carry2 as u64);
        }

        (result, carry != 0)
    }

    pub fn wrapping_add(&self, rhs: &Self) -> Self {
        self.carrying_add(rhs).0
    }

    pub fn borrowing_sub(&self, rhs: &Self) -> (Self, bool) {
        let mut result = U256([0; 4]);
        let mut borrow: u64 = 0;

        for i in 0..4 {
            let (diff1, borrow1) = self.0[i].overflowing_sub(rhs.0[i]);
            let (diff2, borrow2) = diff1.overflowing_sub(borrow);

            result.0[i] = diff2;
            borrow = (borrow1 as u64) + (borrow2 as u64);
        }

        (result, borrow != 0)
    }

    pub fn wrapping_sub(&self, rhs: &Self) -> Self {
        self.borrowing_sub(rhs).0
    }
}

impl Add for U256 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        self.wrapping_add(&rhs)
    }
}

impl<'b> Add<&'b U256> for &U256 {
    type Output = U256;

    fn add(self, rhs: &'b U256) -> Self::Output {
        self.wrapping_add(rhs)
    }
}

impl Sub for U256 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.wrapping_sub(&rhs)
    }
}

impl<'b> Sub<&'b U256> for &U256 {
    type Output = U256;

    fn sub(self, rhs: &'b U256) -> Self::Output {
        self.wrapping_sub(rhs)
    }
}

impl BitXor for U256 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        if is_x86_feature_detected!("avx2") {
            unsafe { crate::arch::x86_64::avx2::xor_avx2(&self, &rhs) }
        } else {
            self.xor_safe(&rhs)
        }
    }
}

impl<'b> BitXor<&'b U256> for &U256 {
    type Output = U256;

    fn bitxor(self, rhs: &'b U256) -> Self::Output {
        if is_x86_feature_detected!("avx2") {
            unsafe { crate::arch::x86_64::avx2::xor_avx2(self, rhs) }
        } else {
            self.xor_safe(rhs)
        }
    }
}

impl Mul for U256 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let full_result = self.full_mul(&rhs);
        U256([
            full_result.0[0],
            full_result.0[1],
            full_result.0[2],
            full_result.0[3],
        ])
    }
}

impl<'b> Mul<&'b U256> for &U256 {
    type Output = U256;

    fn mul(self, rhs: &'b U256) -> Self::Output {
        let full_result = self.full_mul(rhs);
        U256([
            full_result.0[0],
            full_result.0[1],
            full_result.0[2],
            full_result.0[3],
        ])
    }
}
