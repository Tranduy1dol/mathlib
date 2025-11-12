use std::ops::{Add, Mul, Sub};

use crate::core::int::BigInt;
use crate::num::int::u256::U256;

#[repr(align(16))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct U128(pub [u32; 4]);

impl BigInt for U128 {
    const ZERO: Self = Self([0; 4]);
    const ONE: Self = Self([1, 0, 0, 0]);

    #[inline]
    fn carrying_add(&self, rhs: &Self) -> (Self, bool) {
        let mut result = Self::ZERO;
        let mut carry: u64 = 0;
        for i in 0..4 {
            let sum = (self.0[i] as u64) + (rhs.0[i] as u64) + carry;
            result.0[i] = sum as u32;
            carry = sum >> 32;
        }
        (result, carry != 0)
    }

    #[inline]
    fn borrowing_sub(&self, rhs: &Self) -> (Self, bool) {
        let mut result = Self::ZERO;
        let mut borrow: i64 = 0;
        for i in 0..4 {
            let diff = (self.0[i] as i64) - (rhs.0[i] as i64) - borrow;
            result.0[i] = diff as u32;
            borrow = (diff >> 32) & 1;
        }
        (result, borrow != 0)
    }

    #[inline]
    fn conditional_select(a: &Self, b: &Self, condition: bool) -> Self {
        let mask_val = if condition { u32::MAX } else { 0 };
        let mask = Self([mask_val; 4]);

        let mut result = Self::ZERO;
        for i in 0..4 {
            result.0[i] = (a.0[i] & mask.0[i]) | (b.0[i] & !mask.0[i]);
        }
        result
    }
}

impl U128 {
    pub fn full_mul(&self, rhs: &Self) -> U256 {
        let mut result = U256::ZERO; // [u32; 8]

        for i in 0..4 {
            let a_limb = self.0[i] as u64;
            if a_limb == 0 {
                continue;
            }
            let mut carry: u64 = 0;

            for j in 0..4 {
                let product = a_limb * (rhs.0[j] as u64);
                let sum = product + (result.0[i + j] as u64);
                let sum_with_carry = sum + carry;

                result.0[i + j] = sum_with_carry as u32;
                carry = sum_with_carry >> 32;
            }

            let (res, c) = result.0[i + 4].overflowing_add(carry as u32);
            result.0[i + 4] = res;

            let mut k = i + 5;
            let mut carry_u32 = c as u32;
            while carry_u32 != 0 && k < 8 {
                let (res_k, c_k) = result.0[k].overflowing_add(carry_u32);
                result.0[k] = res_k;
                carry_u32 = c_k as u32;
                k += 1;
            }
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
        let mut limbs = [0u32; 4];
        limbs.copy_from_slice(&full_result.0[0..4]);
        Self(limbs)
    }
}
impl std::fmt::Debug for U128 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "U128([0x{:x}, 0x{:x}, 0x{:x}, 0x{:x}])",
            self.0[0], self.0[1], self.0[2], self.0[3]
        )
    }
}
