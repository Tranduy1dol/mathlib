use std::ops::{Add, Sub};

use crate::core::int::BigInt;

#[repr(align(32))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct U256(pub [u32; 8]);

impl BigInt for U256 {
    const ZERO: Self = Self([0; 8]);
    const ONE: Self = Self([1, 0, 0, 0, 0, 0, 0, 0]);

    /// Computes the limb-wise sum of two U256 values and indicates whether a carry out from the most-significant limb occurred.
    ///
    /// # Returns
    ///
    /// `(U256, bool)` — the computed sum and `true` if a carry out from the most-significant limb occurred, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// let a = U256([5, 0, 0, 0, 0, 0, 0, 0]);
    /// let b = U256([10, 0, 0, 0, 0, 0, 0, 0]);
    /// let (sum, carry) = a.carrying_add(&b);
    /// assert_eq!(sum.0[0], 15);
    /// assert!(!carry);
    /// ```
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

    /// Subtracts `rhs` from `self` treating both as 256-bit unsigned integers and returns the difference and a borrow flag.
    ///
    /// The returned tuple is `(difference, borrow)` where `difference` is the 256-bit result of `self - rhs` and `borrow` is
    /// `true` if an underflow (borrow out) occurred, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// let a = U256([5, 0, 0, 0, 0, 0, 0, 0]);
    /// let b = U256([3, 0, 0, 0, 0, 0, 0, 0]);
    /// let (res, borrow) = a.borrowing_sub(&b);
    /// assert_eq!(res.0[0], 2);
    /// assert!(!borrow);
    ///
    /// let zero = U256::ZERO;
    /// let one = U256::ONE;
    /// let (underflow_res, underflow) = zero.borrowing_sub(&one);
    /// assert!(underflow);
    /// assert_eq!(underflow_res, U256([u32::MAX; 8]));
    /// ```
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
    /// Selects one of two `U256` values according to `condition`.
    ///
    /// Returns `a` when `condition` is `true`, otherwise returns `b`. When running on x86_64 with
    /// AVX2 available this selection may use an accelerated CPU-specific implementation; otherwise a
    /// constant-time per-limb selection is used.
    ///
    /// # Examples
    ///
    /// ```
    /// let a = U256([1, 0, 0, 0, 0, 0, 0, 0]);
    /// let b = U256([2, 0, 0, 0, 0, 0, 0, 0]);
    /// assert_eq!(U256::conditional_select(&a, &b, true), a);
    /// assert_eq!(U256::conditional_select(&a, &b, false), b);
    /// ```
    pub fn conditional_select(a: &Self, b: &Self, condition: bool) -> Self {
        let mask_val = if condition { u32::MAX } else { 0 };
        let mask = Self([mask_val; 8]);

        #[cfg(target_arch = "x86_64")]
        if is_x86_feature_detected!("avx2") {
            unsafe { crate::arch::x86_64::avx2::u256_conditional_select_avx2(a, b, &mask) }
        } else {
            let mut result = Self::ZERO;
            for i in 0..8 {
                result.0[i] = (a.0[i] & mask.0[i]) | (b.0[i] & !mask.0[i]);
            }
            result
        }
    }
}

impl Add for U256 {
    type Output = Self;

    /// Adds two `U256` values and returns their 256-bit sum.
    ///
    /// The result is the lower 256 bits of the mathematical sum (i.e., addition wraps modulo 2^256).
    ///
    /// # Examples
    ///
    /// ```
    /// let a = U256([1, 0, 0, 0, 0, 0, 0, 0]);
    /// let b = U256([2, 0, 0, 0, 0, 0, 0, 0]);
    /// let sum = a + b;
    /// assert_eq!(sum, U256([3, 0, 0, 0, 0, 0, 0, 0]));
    /// ```
    fn add(self, rhs: Self) -> Self::Output {
        self.carrying_add(&rhs).0
    }
}

impl<'b> Add<&'b U256> for &U256 {
    type Output = U256;

    /// Compute the arithmetic sum of two U256 values.
    ///
    /// # Returns
    ///
    /// `U256` containing the sum of the operands.
    ///
    /// # Examples
    ///
    /// ```
    /// let a = U256([1, 0, 0, 0, 0, 0, 0, 0]);
    /// let b = U256([2, 0, 0, 0, 0, 0, 0, 0]);
    /// let sum = &a + &b;
    /// assert_eq!(sum, U256([3, 0, 0, 0, 0, 0, 0, 0]));
    /// ```
    fn add(self, rhs: &'b U256) -> Self::Output {
        self.carrying_add(rhs).0
    }
}

impl Sub for U256 {
    type Output = Self;

    /// Subtracts `rhs` from `self` and returns the resulting `U256`.
    ///
    /// # Examples
    ///
    /// ```
    /// let a = U256([15, 0, 0, 0, 0, 0, 0, 0]);
    /// let b = U256([10, 0, 0, 0, 0, 0, 0, 0]);
    /// let r = a - b;
    /// assert_eq!(r.0[0], 5);
    /// ```
    fn sub(self, rhs: Self) -> Self::Output {
        self.borrowing_sub(&rhs).0
    }
}

impl<'b> Sub<&'b U256> for &U256 {
    type Output = U256;

    /// Subtracts two 256-bit values provided by reference and returns their difference.
    ///
    /// # Examples
    ///
    /// ```
    /// let a = U256([15, 0, 0, 0, 0, 0, 0, 0]);
    /// let b = U256([10, 0, 0, 0, 0, 0, 0, 0]);
    /// let r = &a - &b;
    /// assert_eq!(r, U256([5, 0, 0, 0, 0, 0, 0, 0]));
    /// ```
    fn sub(self, rhs: &'b U256) -> Self::Output {
        self.borrowing_sub(rhs).0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Constructs a U256 from a 64-bit unsigned integer.
    ///
    /// The lower 64 bits of the returned `U256` are set to `val` (low 32 bits in limb 0,
    /// high 32 bits in limb 1); all remaining limbs are zero.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = from_u64(0x0000_0001_0000_0002u64);
    /// assert_eq!(x.0[0], 0x0000_0002u32);
    /// assert_eq!(x.0[1], 0x0000_0001u32);
    /// assert!(x.0.iter().skip(2).all(|&limb| limb == 0));
    /// ```
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