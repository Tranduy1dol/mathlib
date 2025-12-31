//! Signed 1024-bit integer implementation.
//!
//! This module provides `I1024`, a signed big integer type that uses `U1024`
//! for its magnitude and a separate sign flag. This is useful for algorithms
//! like the Extended Euclidean Algorithm where intermediate values can be negative.

use std::fmt;
use std::ops::{Add, Mul, Neg, Sub};

use super::u1024::U1024;

/// A signed 1024-bit integer.
///
/// Represented as a magnitude (absolute value) and a sign flag.
/// The value is positive when `positive` is true, negative when false.
/// Zero is always represented with `positive = true`.
///
/// # Examples
///
/// ```
/// use lumen_math::I1024;
///
/// let a = I1024::from_u64(42);
/// let b = -a;
///
/// assert!(a.is_positive());
/// assert!(b.is_negative());
/// assert_eq!(a.magnitude(), b.magnitude());
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct I1024 {
    /// The absolute value (magnitude).
    magnitude: U1024,
    /// Sign: true for positive or zero, false for negative.
    positive: bool,
}

impl I1024 {
    /// Zero value.
    pub const ZERO: Self = Self {
        magnitude: U1024::ZERO,
        positive: true,
    };

    /// One value.
    pub const ONE: Self = Self {
        magnitude: U1024([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        positive: true,
    };

    /// Negative one.
    pub const NEG_ONE: Self = Self {
        magnitude: U1024([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        positive: false,
    };

    /// Creates a new I1024 from a magnitude and sign.
    ///
    /// # Arguments
    ///
    /// * `magnitude` - The absolute value
    /// * `positive` - true for positive, false for negative
    #[inline]
    pub const fn new(magnitude: U1024, positive: bool) -> Self {
        // Zero is always positive
        if magnitude.0[0] == 0
            && magnitude.0[1] == 0
            && magnitude.0[2] == 0
            && magnitude.0[3] == 0
            && magnitude.0[4] == 0
            && magnitude.0[5] == 0
            && magnitude.0[6] == 0
            && magnitude.0[7] == 0
            && magnitude.0[8] == 0
            && magnitude.0[9] == 0
            && magnitude.0[10] == 0
            && magnitude.0[11] == 0
            && magnitude.0[12] == 0
            && magnitude.0[13] == 0
            && magnitude.0[14] == 0
            && magnitude.0[15] == 0
        {
            return Self {
                magnitude,
                positive: true,
            };
        }
        Self {
            magnitude,
            positive,
        }
    }

    /// Creates a positive I1024 from a U1024.
    #[inline]
    pub const fn from_unsigned(value: U1024) -> Self {
        Self::new(value, true)
    }

    /// Creates an I1024 from a u64 value.
    #[inline]
    pub fn from_u64(value: u64) -> Self {
        Self::new(U1024::from_u64(value), true)
    }

    /// Creates a negative I1024 from a u64 value.
    #[inline]
    pub fn from_u64_neg(value: u64) -> Self {
        if value == 0 {
            Self::ZERO
        } else {
            Self::new(U1024::from_u64(value), false)
        }
    }

    /// Returns the magnitude (absolute value) as U1024.
    #[inline]
    pub const fn magnitude(&self) -> U1024 {
        self.magnitude
    }

    /// Returns true if this value is positive or zero.
    #[inline]
    pub const fn is_positive(&self) -> bool {
        self.positive
    }

    /// Returns true if this value is strictly negative (less than zero).
    #[inline]
    pub fn is_negative(&self) -> bool {
        !self.positive && self.magnitude != U1024::ZERO
    }

    /// Returns true if this value is zero.
    #[inline]
    pub fn is_zero(&self) -> bool {
        self.magnitude == U1024::ZERO
    }

    /// Returns the absolute value.
    #[inline]
    pub const fn abs(&self) -> Self {
        Self {
            magnitude: self.magnitude,
            positive: true,
        }
    }

    /// Computes self - (quotient * other).
    ///
    /// This is a specialized operation used in the Extended Euclidean Algorithm.
    ///
    /// # Panics
    ///
    /// Panics if `quotient * other` exceeds 1024 bits (overflow).
    /// This method is intended solely for internal protocol usage where bounds are known.
    pub(crate) fn sub_mul(&self, quotient: &U1024, other: &I1024) -> Self {
        // Compute quotient * other.magnitude
        let (prod_lo, prod_hi) = quotient.const_mul(&other.magnitude);

        if prod_hi != U1024::ZERO {
            panic!("sub_mul: multiplication overflowed 1024 bits");
        }

        // Sign of quotient * other is same as other.positive (quotient is always positive)
        let prod_positive = other.positive;

        // Now compute self - prod
        if self.positive == prod_positive {
            // Same sign: subtract magnitudes
            if self.magnitude >= prod_lo {
                Self::new(self.magnitude - prod_lo, self.positive)
            } else {
                Self::new(prod_lo - self.magnitude, !self.positive)
            }
        } else {
            // Different signs: add magnitudes, keep sign of self
            // Note: This addition can conceptually overflow I1024 if result > 2^1024,
            // but we perform wrapping addition on U1024 magnitudes here.
            // In the context of Extended GCD, intermediate values shouldn't exceed bounds unexpectedly.
            Self::new(self.magnitude + prod_lo, self.positive)
        }
    }
}

impl Default for I1024 {
    fn default() -> Self {
        Self::ZERO
    }
}

impl From<U1024> for I1024 {
    fn from(value: U1024) -> Self {
        Self::from_unsigned(value)
    }
}

impl From<u64> for I1024 {
    fn from(value: u64) -> Self {
        Self::from_u64(value)
    }
}

impl From<i64> for I1024 {
    fn from(value: i64) -> Self {
        if value >= 0 {
            Self::from_u64(value as u64)
        } else {
            Self::from_u64_neg(value.unsigned_abs())
        }
    }
}

impl Neg for I1024 {
    type Output = Self;

    fn neg(self) -> Self {
        if self.magnitude == U1024::ZERO {
            self
        } else {
            Self {
                magnitude: self.magnitude,
                positive: !self.positive,
            }
        }
    }
}

impl Add for I1024 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        if self.positive == rhs.positive {
            // Same sign: add magnitudes
            Self::new(self.magnitude + rhs.magnitude, self.positive)
        } else {
            // Different signs: subtract magnitudes
            if self.magnitude >= rhs.magnitude {
                Self::new(self.magnitude - rhs.magnitude, self.positive)
            } else {
                Self::new(rhs.magnitude - self.magnitude, rhs.positive)
            }
        }
    }
}

impl Sub for I1024 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        self + (-rhs)
    }
}

impl Mul for I1024 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        let (result, _) = self.magnitude.const_mul(&rhs.magnitude);
        let positive = self.positive == rhs.positive;
        Self::new(result, positive)
    }
}

impl fmt::Display for I1024 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.positive && self.magnitude != U1024::ZERO {
            write!(f, "-")?;
        }
        write!(f, "{}", self.magnitude)
    }
}

/// Macro to create an I1024 value.
///
/// # Examples
///
/// ```
/// use lumen_math::i1024;
///
/// // From positive literal (use u64 suffix)
/// let a = i1024!(42u64);
///
/// // From negative literal
/// let b = i1024!(-42);
///
/// // From U1024
/// use lumen_math::U1024;
/// let c = i1024!(U1024::from_u64(100));
/// ```
#[macro_export]
macro_rules! i1024 {
    // Negative integer literal
    (- $val:expr) => {{ $crate::I1024::from_u64_neg($val as u64) }};
    // Positive value or U1024
    ($val:expr) => {{ $crate::I1024::from($val) }};
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_i1024_zero() {
        let z = I1024::ZERO;
        assert!(z.is_zero());
        assert!(z.is_positive());
        assert!(!z.is_negative());
    }

    #[test]
    fn test_i1024_from_u64() {
        let a = I1024::from_u64(42);
        assert!(a.is_positive());
        assert_eq!(a.magnitude(), U1024::from_u64(42));
    }

    #[test]
    fn test_i1024_negation() {
        let a = I1024::from_u64(42);
        let b = -a;

        assert!(a.is_positive());
        assert!(b.is_negative());
        assert_eq!(a.magnitude(), b.magnitude());

        // Negate zero stays zero
        let z = I1024::ZERO;
        let nz = -z;
        assert!(nz.is_positive());
        assert!(nz.is_zero());
    }

    #[test]
    fn test_i1024_addition() {
        let a = I1024::from_u64(10);
        let b = I1024::from_u64(20);

        // Positive + Positive
        let c = a + b;
        assert!(c.is_positive());
        assert_eq!(c.magnitude(), U1024::from_u64(30));

        // Positive + Negative (larger positive)
        let d = I1024::from_u64(30);
        let e = -I1024::from_u64(10);
        let f = d + e;
        assert!(f.is_positive());
        assert_eq!(f.magnitude(), U1024::from_u64(20));

        // Positive + Negative (larger negative)
        let g = I1024::from_u64(10);
        let h = -I1024::from_u64(30);
        let i = g + h;
        assert!(i.is_negative());
        assert_eq!(i.magnitude(), U1024::from_u64(20));
    }

    #[test]
    fn test_i1024_subtraction() {
        let a = I1024::from_u64(30);
        let b = I1024::from_u64(10);

        let c = a - b;
        assert!(c.is_positive());
        assert_eq!(c.magnitude(), U1024::from_u64(20));

        let d = b - a;
        assert!(d.is_negative());
        assert_eq!(d.magnitude(), U1024::from_u64(20));
    }

    #[test]
    fn test_i1024_multiplication() {
        let a = I1024::from_u64(6);
        let b = I1024::from_u64(7);

        let c = a * b;
        assert!(c.is_positive());
        assert_eq!(c.magnitude(), U1024::from_u64(42));

        // Positive * Negative
        let d = a * (-b);
        assert!(d.is_negative());
        assert_eq!(d.magnitude(), U1024::from_u64(42));

        // Negative * Negative
        let e = (-a) * (-b);
        assert!(e.is_positive());
        assert_eq!(e.magnitude(), U1024::from_u64(42));
    }

    #[test]
    fn test_i1024_sub_mul() {
        // Test the specialized sub_mul operation
        let a = I1024::from_u64(100);
        let quotient = U1024::from_u64(3);
        let other = I1024::from_u64(20);

        // 100 - 3*20 = 100 - 60 = 40
        let result = a.sub_mul(&quotient, &other);
        assert!(result.is_positive());
        assert_eq!(result.magnitude(), U1024::from_u64(40));

        // 50 - 3*20 = 50 - 60 = -10
        let b = I1024::from_u64(50);
        let result2 = b.sub_mul(&quotient, &other);
        assert!(result2.is_negative());
        assert_eq!(result2.magnitude(), U1024::from_u64(10));
    }

    #[test]
    fn test_i1024_from_i64() {
        let a = I1024::from(-42i64);
        assert!(a.is_negative());
        assert_eq!(a.magnitude(), U1024::from_u64(42));

        let b = I1024::from(42i64);
        assert!(b.is_positive());
        assert_eq!(b.magnitude(), U1024::from_u64(42));
    }

    #[test]
    fn test_i1024_display() {
        let a = I1024::from_u64(42);
        let b = -I1024::from_u64(42);
        let z = I1024::ZERO;

        assert!(!format!("{}", a).contains('-'));
        assert!(format!("{}", b).contains('-'));
        assert!(!format!("{}", z).contains('-'));
    }

    #[test]
    #[should_panic(expected = "sub_mul: multiplication overflowed 1024 bits")]
    fn test_i1024_sub_mul_overflow() {
        // Construct MAX manually since it's not a const on U1024
        let max_digits = [u64::MAX; 16];
        let large = U1024(max_digits);

        // 2 * MAX will definitely overflow 1024 bits
        let other = I1024::from_u64(2);
        let base = I1024::from_u64(1);

        base.sub_mul(&large, &other);
    }
}
