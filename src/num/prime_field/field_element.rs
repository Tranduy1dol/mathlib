use std::ops::{Add, Mul, Sub};

use crate::core::{field::Field, int::BigInt};
use crate::num::int::u256::U256;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FieldElement {
    pub inner: U256,
    pub modulus: U256,
}

impl FieldElement {
    /// Create a FieldElement from a raw value and a modulus.
    ///
    /// The provided `val` is stored directly as the element's `inner` value; it is not reduced or normalized modulo `modulus`.
    ///
    /// # Examples
    ///
    /// ```
    /// let fe = FieldElement::new(U256::from(5u64), U256::from(19u64));
    /// assert_eq!(fe.inner, U256::from(5u64));
    /// assert_eq!(fe.modulus, U256::from(19u64));
    /// ```
    pub fn new(val: U256, modulus: U256) -> Self {
        Self {
            inner: val,
            modulus,
        }
    }
}

impl Add for FieldElement {
    type Output = Self;

    /// Adds two field elements modulo their common modulus, returning the sum reduced into the field.
    ///
    /// The resulting element is the canonical representative in the range [0, modulus - 1].
    ///
    /// # Examples
    ///
    /// ```
    /// let a = FieldElement::new(U256::from(12u64), U256::from(19u64));
    /// let b = FieldElement::new(U256::from(15u64), U256::from(19u64));
    /// let c = a + b; // 12 + 15 = 27 ≡ 8 (mod 19)
    /// assert_eq!(c.inner, U256::from(8u64));
    /// ```
    fn add(self, rhs: Self) -> Self::Output {
        debug_assert_eq!(self.modulus, rhs.modulus);

        let (sum, _carry) = self.inner.carrying_add(&rhs.inner);
        let (sum_norm, borrow) = sum.borrowing_sub(&self.modulus);

        let inner = U256::conditional_select(&sum_norm, &sum, !borrow);

        Self {
            inner,
            modulus: self.modulus,
        }
    }
}

impl Sub for FieldElement {
    type Output = Self;

    /// Subtracts one field element from another and reduces the result modulo the element's modulus.
    ///
    /// Panics in debug builds if the two operands have different moduli.
    ///
    /// # Examples
    ///
    /// ```
    /// // subtract 15 from 8 modulo 19 => 8 - 15 = -7 ≡ 12 (mod 19)
    /// let a = FieldElement::new(U256::from(8u64), U256::from(19u64));
    /// let b = FieldElement::new(U256::from(15u64), U256::from(19u64));
    /// let c = a - b;
    /// assert_eq!(c.inner, U256::from(12u64));
    /// ```
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
    /// Performs modular multiplication of two `FieldElement` values using Montgomery reduction.
    ///
    /// The result is the product of the two elements reduced modulo their shared modulus.
    ///
    /// # Panics
    ///
    /// Panics with message `"Multiplication requires Montgomery Reduction"` because Montgomery
    /// reduction is not implemented.
    ///
    /// # Examples
    ///
    /// ```should_panic
    /// // Construct two field elements with the same modulus (helpers omitted).
    /// // Calling multiplication currently panics because Montgomery reduction is required.
    /// let a = FieldElement::new(u256_from_u64(2), u256_from_u64(19));
    /// let b = FieldElement::new(u256_from_u64(3), u256_from_u64(19));
    /// let _ = a * b;
    /// ```
    fn mul(self, _rhs: Self) -> Self::Output {
        unimplemented!("Multiplication requires Montgomery Reduction");
    }
}

impl Field for FieldElement {}

#[cfg(test)]
mod tests {
    use super::*;

    // Helper to create a U256 from a single u64 value for tests.
    /// Constructs a U256 representing the given 64-bit unsigned integer.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = u256_from_u64(0x1_0000_0000u64);
    /// assert_eq!(x, U256([0u32, 1u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32]));
    /// ```
    fn u256_from_u64(val: u64) -> U256 {
        let mut limbs = [0; 8];
        limbs[0] = val as u32;
        limbs[1] = (val >> 32) as u32;
        U256(limbs)
    }

    // Helper to create a FieldElement with a fixed modulus for tests.
    // We'll use a small prime modulus, P = 19.
    /// Constructs a `FieldElement` representing `val` in the prime field with modulus 19.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = fe(7);
    /// assert_eq!(x, FieldElement::new(u256_from_u64(7), u256_from_u64(19)));
    /// ```
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

    /// Verifies modular addition for FieldElement with modulus 19, covering normal addition, wrap-around, exact modulus, and adding zero.
    ///
    /// # Examples
    ///
    /// ```
    /// // Normal addition: 7 + 8 = 15 (mod 19)
    /// assert_eq!(fe(7) + fe(8), fe(15));
    /// // Wrap-around: 12 + 15 = 27 = 8 (mod 19)
    /// assert_eq!(fe(12) + fe(15), fe(8));
    /// // Exact modulus: 10 + 9 = 19 = 0 (mod 19)
    /// assert_eq!(fe(10) + fe(9), fe(0));
    /// // Adding zero
    /// assert_eq!(fe(17) + fe(0), fe(17));
    /// ```
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
}