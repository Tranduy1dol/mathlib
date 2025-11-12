use std::ops::{Add, Sub};

use crate::core::int::BigInt;
use crate::num::int::u256::U256;

#[repr(align(32))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct U512(pub [u32; 16]);

impl BigInt for U512 {
    const ZERO: Self = Self([0; 16]);
    const ONE: Self = Self([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);

    #[inline]
    fn carrying_add(&self, rhs: &Self) -> (Self, bool) {
        let mut result = Self::ZERO;
        let mut carry: u64 = 0;

        for i in 0..16 {
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

        for i in 0..16 {
            let diff = (self.0[i] as i64) - (rhs.0[i] as i64) - borrow;
            result.0[i] = diff as u32;
            borrow = (diff >> 32) & 1;
        }
        (result, borrow != 0)
    }

    #[inline]
    fn conditional_select(a: &Self, b: &Self, condition: bool) -> Self {
        let mask_val = if condition { u32::MAX } else { 0 };
        let mask = Self([mask_val; 16]);

        let mut result = Self::ZERO;
        for i in 0..16 {
            result.0[i] = (a.0[i] & mask.0[i]) | (b.0[i] & !mask.0[i]);
        }
        result
    }
}

impl Add for U512 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        self.carrying_add(&rhs).0
    }
}

impl Sub for U512 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        self.borrowing_sub(&rhs).0
    }
}

impl std::fmt::Debug for U512 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "U512([")?;
        for i in 0..15 {
            write!(f, "0x{:x}, ", self.0[i])?;
        }
        write!(f, "0x{:x}])", self.0[15])
    }
}

impl From<U256> for U512 {
    fn from(value: U256) -> Self {
        let mut limbs = [0u32; 16];
        limbs[0..8].copy_from_slice(&value.0);
        Self(limbs)
    }
}
