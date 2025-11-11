use std::ops::{Add, Mul, Sub};

use crate::core::{field::Field, int::BigInt};
use crate::num::int::u256::U256;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FieldElement {
    pub inner: U256,
    pub modulus: U256,
}

impl FieldElement {
    pub fn new(val: U256, modulus: U256) -> Self {
        debug_assert!(modulus != U256::ZERO, "modulus must be non-zero");

        let mut inner = val;
        loop {
            let (candidate, borrow) = inner.borrowing_sub(&modulus);
            if borrow {
                break;
            }
            inner = candidate;
        }

        Self { inner, modulus }
    }
}

impl Add for FieldElement {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        debug_assert_eq!(self.modulus, rhs.modulus);

        let (sum, carry) = self.inner.carrying_add(&rhs.inner);
        let (sum_norm, borrow) = sum.borrowing_sub(&self.modulus);

        let use_reduced = !borrow || carry;
        let inner = U256::conditional_select(&sum_norm, &sum, use_reduced);

        Self {
            inner,
            modulus: self.modulus,
        }
    }
}

impl Sub for FieldElement {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        debug_assert_eq!(self.modulus, rhs.modulus);

        let (diff, borrow) = self.inner.borrowing_sub(&rhs.inner);
        let (diff_norm, _carry) = diff.carrying_add(&self.modulus);

        let inner = U256::conditional_select(&diff_norm, &diff, borrow);

        Self {
            inner,
            modulus: self.modulus,
        }
    }
}

impl Mul for FieldElement {
    type Output = Self;
    fn mul(self, _rhs: Self) -> Self::Output {
        unimplemented!("Multiplication requires Montgomery Reduction");
    }
}

impl Field for FieldElement {}

#[cfg(test)]
mod tests {
    use super::*;

    // Helper to create a U256 from a single u64 value for tests.
    fn u256_from_u64(val: u64) -> U256 {
        let mut limbs = [0; 8];
        limbs[0] = val as u32;
        limbs[1] = (val >> 32) as u32;
        U256(limbs)
    }

    // Helper to create a FieldElement with a fixed modulus for tests.
    // We'll use a small prime modulus, P = 19.
    fn fe(val: u64) -> FieldElement {
        let modulus = u256_from_u64(19);
        FieldElement::new(u256_from_u64(val), modulus)
    }

    #[test]
    fn test_new() {
        let val = u256_from_u64(5);
        let modulus = u256_from_u64(19);
        let fe = FieldElement::new(val, modulus);
        assert_eq!(fe.inner, val);
        assert_eq!(fe.modulus, modulus);
    }

    #[test]
    fn test_add() {
        // Case 1: a + b < modulus
        // 7 + 8 = 15 (mod 19)
        let a = fe(7);
        let b = fe(8);
        let expected = fe(15);
        assert_eq!(a + b, expected);

        // Case 2: a + b > modulus (wraps around)
        // 12 + 15 = 27 = 8 (mod 19)
        let a = fe(12);
        let b = fe(15);
        let expected = fe(8);
        assert_eq!(a + b, expected);

        // Case 3: a + b == modulus
        // 10 + 9 = 19 = 0 (mod 19)
        let a = fe(10);
        let b = fe(9);
        let expected = fe(0);
        assert_eq!(a + b, expected);

        // Case 4: Adding zero
        let a = fe(17);
        let b = fe(0);
        assert_eq!(a + b, a);
    }

    #[test]
    fn test_sub() {
        // Case 1: a - b >= 0
        // 15 - 8 = 7 (mod 19)
        let a = fe(15);
        let b = fe(8);
        let expected = fe(7);
        assert_eq!(a - b, expected);

        // Case 2: a - b < 0 (wraps around)
        // 8 - 15 = -7 = 12 (mod 19)
        let a = fe(8);
        let b = fe(15);
        let expected = fe(12);
        assert_eq!(a - b, expected);

        // Case 3: Subtracting to zero
        // 10 - 10 = 0 (mod 19)
        let a = fe(10);
        let b = fe(10);
        let expected = fe(0);
        assert_eq!(a - b, expected);

        // Case 4: Subtracting zero
        let a = fe(5);
        let b = fe(0);
        assert_eq!(a - b, a);
    }

    #[test]
    fn test_add_with_wraparound() {
        // Test addition that overflows U256.
        // Let modulus = 2^256 - 1.
        let modulus = U256([u32::MAX; 8]);

        // Let a = modulus - 1 and b = 2.
        let a_val = modulus.borrowing_sub(&U256::ONE).0;
        let b_val = u256_from_u64(2);

        let a = FieldElement::new(a_val, modulus);
        let b = FieldElement::new(b_val, modulus);

        // (modulus - 1) + 2 = modulus + 1.
        // The raw sum overflows U256, resulting in a value of 1 with a carry.
        // The correct result mod (2^256 - 1) is 1.
        let result = a + b;
        assert_eq!(result.inner, U256::ONE);
    }
}
