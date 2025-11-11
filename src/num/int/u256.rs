use std::ops::{Add, Sub};

use crate::core::int::BigInt;

#[repr(align(32))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct U256(pub [u32; 8]);

impl BigInt for U256 {
    const ZERO: Self = Self([0; 8]);
    const ONE: Self = Self([1, 0, 0, 0, 0, 0, 0, 0]);

    #[inline]
    fn carrying_add(&self, rhs: &Self) -> (Self, bool) {
        let mut result = Self::ZERO;
        let mut carry: u64 = 0; // Cờ nhớ là u64

        for i in 0..8 {
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

        for i in 0..8 {
            // (a[i] - b[i] - borrow)
            let diff = (self.0[i] as i64) - (rhs.0[i] as i64) - borrow;
            result.0[i] = diff as u32;
            borrow = (diff >> 32) & 1;
        }
        (result, borrow != 0)
    }
}

impl U256 {
    pub fn conditional_select(a: &Self, b: &Self, condition: bool) -> Self {
        let mask_val = if condition { u32::MAX } else { 0 };
        let mask = Self([mask_val; 8]);

        #[cfg(target_arch = "x86_64")]
        if is_x86_feature_detected!("avx2") {
            return unsafe { crate::arch::x86_64::avx2::u256_conditional_select_avx2(a, b, &mask) };
        }

        let mut result = Self::ZERO;
        for i in 0..8 {
            result.0[i] = (a.0[i] & mask.0[i]) | (b.0[i] & !mask.0[i]);
        }
        result
    }
}

impl Add for U256 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        self.carrying_add(&rhs).0
    }
}

impl<'b> Add<&'b U256> for &U256 {
    type Output = U256;

    fn add(self, rhs: &'b U256) -> Self::Output {
        self.carrying_add(rhs).0
    }
}

impl Sub for U256 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.borrowing_sub(&rhs).0
    }
}

impl<'b> Sub<&'b U256> for &U256 {
    type Output = U256;

    fn sub(self, rhs: &'b U256) -> Self::Output {
        self.borrowing_sub(rhs).0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper to create a U256 from a single u64 value.
    fn from_u64(val: u64) -> U256 {
        let mut limbs = [0; 8];
        limbs[0] = val as u32;
        limbs[1] = (val >> 32) as u32;
        U256(limbs)
    }

    #[test]
    fn test_constants() {
        assert_eq!(U256::ZERO, from_u64(0));
        assert_eq!(U256::ONE, from_u64(1));
    }

    #[test]
    fn test_carrying_add() {
        // Simple case: 5 + 10 = 15
        let a = from_u64(5);
        let b = from_u64(10);
        let (result, carry) = a.carrying_add(&b);
        assert_eq!(result, from_u64(15));
        assert!(!carry);

        // Addition with carry between limbs
        let a = from_u64(u32::MAX as u64);
        let b = from_u64(1);
        let (result, carry) = a.carrying_add(&b);
        assert_eq!(result, from_u64(1 << 32));
        assert!(!carry);

        // Addition that overflows the U256
        let max = U256([u32::MAX; 8]);
        let one = U256::ONE;
        let (result, carry) = max.carrying_add(&one);
        assert_eq!(result, U256::ZERO);
        assert!(carry);

        // Add with reference operator
        let c = from_u64(100);
        let d = from_u64(200);
        assert_eq!(&c + &d, from_u64(300));
    }

    #[test]
    fn test_borrowing_sub() {
        // Simple case: 15 - 10 = 5
        let a = from_u64(15);
        let b = from_u64(10);
        let (result, borrow) = a.borrowing_sub(&b);
        assert_eq!(result, from_u64(5));
        assert!(!borrow);

        // Subtraction with borrow between limbs
        let a = from_u64(1 << 32);
        let b = from_u64(1);
        let (result, borrow) = a.borrowing_sub(&b);
        assert_eq!(result, from_u64(u32::MAX as u64));
        assert!(!borrow);

        // Subtraction that underflows the U256
        let zero = U256::ZERO;
        let one = U256::ONE;
        let (result, borrow) = zero.borrowing_sub(&one);
        assert_eq!(result, U256([u32::MAX; 8]));
        assert!(borrow);

        // Subtracting a number from itself
        let a = from_u64(123456789);
        let (result, borrow) = a.borrowing_sub(&a);
        assert_eq!(result, U256::ZERO);
        assert!(!borrow);

        // Sub with reference operator
        let c = from_u64(300);
        let d = from_u64(200);
        assert_eq!(&c - &d, from_u64(100));
    }

    #[test]
    fn test_conditional_select() {
        let a = from_u64(0x_DEAD_BEEF_CAFE_BABE);
        let b = from_u64(0x_1234_5678_9ABC_DEF0);

        // When condition is true, select `a`
        let result_true = U256::conditional_select(&a, &b, true);
        assert_eq!(result_true, a);

        // When condition is false, select `b`
        let result_false = U256::conditional_select(&a, &b, false);
        assert_eq!(result_false, b);
    }

    #[test]
    fn test_operator_overloads() {
        let a = from_u64(100);
        let b = from_u64(50);

        // Add
        assert_eq!(a + b, from_u64(150));

        // Sub
        assert_eq!(a - b, from_u64(50));
    }
}
