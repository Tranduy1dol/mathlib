//! Extended Euclidean Algorithm implementation for U1024.
//!
//! The Extended Euclidean Algorithm computes the GCD of two integers and also
//! finds the Bézout coefficients (x, y) such that: ax + by = gcd(a, b)
//!
//! This is fundamental for computing modular inverses and is used extensively
//! in cryptographic applications.

use crate::big_int::{I1024, U1024};

/// Result of the Extended Euclidean Algorithm.
///
/// Contains the GCD and the Bézout coefficients.
/// Note: For U1024 (unsigned), we track signs separately via `I1024`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExtendedGcdResult {
    /// The greatest common divisor of a and b.
    pub gcd: U1024,
    /// Bézout coefficient x (signed).
    pub x: I1024,
    /// Bézout coefficient y (signed).
    pub y: I1024,
}

impl ExtendedGcdResult {
    /// Returns the absolute value of x as U1024.
    #[inline]
    pub fn x_magnitude(&self) -> U1024 {
        self.x.magnitude()
    }

    /// Returns true if x is positive or zero.
    #[inline]
    pub fn x_positive(&self) -> bool {
        self.x.is_positive()
    }

    /// Returns the absolute value of y as U1024.
    #[inline]
    pub fn y_magnitude(&self) -> U1024 {
        self.y.magnitude()
    }

    /// Returns true if y is positive or zero.
    #[inline]
    pub fn y_positive(&self) -> bool {
        self.y.is_positive()
    }
}

/// Computes the Extended Euclidean Algorithm for two U1024 integers.
///
/// Given non-negative integers a and b, computes:
/// - gcd(a, b): the greatest common divisor
/// - x, y: Bézout coefficients such that gcd = a*x + b*y (with signs)
///
/// # Arguments
///
/// * `a` - First non-negative integer
/// * `b` - Second non-negative integer
///
/// # Returns
///
/// An `ExtendedGcdResult` containing the GCD and Bézout coefficients.
///
/// # Examples
///
/// ```
/// use lumen_math::protocol::extended_gcd;
/// use lumen_math::U1024;
///
/// let a = U1024::from_u64(30);
/// let b = U1024::from_u64(20);
/// let result = extended_gcd(a, b);
///
/// // gcd(30, 20) = 10
/// assert_eq!(result.gcd, U1024::from_u64(10));
/// ```
pub fn extended_gcd(a: U1024, b: U1024) -> ExtendedGcdResult {
    if b == U1024::ZERO {
        return ExtendedGcdResult {
            gcd: a,
            x: I1024::ONE,
            y: I1024::ZERO,
        };
    }

    // Extended Euclidean Algorithm using iterative approach
    let mut old_r = a;
    let mut r = b;
    let mut old_s = I1024::ONE;
    let mut s = I1024::ZERO;
    let mut old_t = I1024::ZERO;
    let mut t = I1024::ONE;

    while r != U1024::ZERO {
        // quotient = old_r / r
        let quotient = old_r / r;

        // Update r: temp = r; r = old_r - quotient * r; old_r = temp
        let temp_r = r;
        let (prod_lo, _) = quotient.const_mul(&r);
        r = old_r - prod_lo;
        old_r = temp_r;

        // Update s: temp = s; s = old_s - quotient * s; old_s = temp
        let temp_s = s;
        s = old_s.sub_mul(&quotient, &s);
        old_s = temp_s;

        // Update t: temp = t; t = old_t - quotient * t; old_t = temp
        let temp_t = t;
        t = old_t.sub_mul(&quotient, &t);
        old_t = temp_t;
    }

    ExtendedGcdResult {
        gcd: old_r,
        x: old_s,
        y: old_t,
    }
}

/// Computes the modular inverse of a modulo m using the Extended Euclidean Algorithm.
///
/// Returns `Some(x)` where `a * x ≡ 1 (mod m)`, or `None` if the inverse doesn't exist
/// (i.e., when gcd(a, m) ≠ 1).
///
/// # Arguments
///
/// * `a` - The value to invert
/// * `m` - The modulus (must be positive)
///
/// # Examples
///
/// ```
/// use lumen_math::protocol::mod_inverse;
/// use lumen_math::U1024;
///
/// // 3^(-1) mod 7 = 5, since 3*5 = 15 ≡ 1 (mod 7)
/// let result = mod_inverse(U1024::from_u64(3), U1024::from_u64(7));
/// assert_eq!(result, Some(U1024::from_u64(5)));
/// ```
pub fn mod_inverse(a: U1024, m: U1024) -> Option<U1024> {
    let result = extended_gcd(a, m);

    if result.gcd != U1024::from_u64(1) {
        return None;
    }

    if result.x.is_positive() {
        // x is positive, return x mod m
        Some(result.x.magnitude() % m)
    } else {
        // x is negative, return m - (|x| mod m)
        let x_mod = result.x.magnitude() % m;
        if x_mod == U1024::ZERO {
            Some(U1024::ZERO)
        } else {
            Some(m - x_mod)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extended_gcd_basic() {
        let a = U1024::from_u64(30);
        let b = U1024::from_u64(20);
        let result = extended_gcd(a, b);
        assert_eq!(result.gcd, U1024::from_u64(10));
    }

    #[test]
    fn test_extended_gcd_coprime() {
        let a = U1024::from_u64(17);
        let b = U1024::from_u64(13);
        let result = extended_gcd(a, b);
        assert_eq!(result.gcd, U1024::from_u64(1));
    }

    #[test]
    fn test_extended_gcd_one_is_zero() {
        let a = U1024::from_u64(10);
        let b = U1024::ZERO;
        let result = extended_gcd(a, b);
        assert_eq!(result.gcd, U1024::from_u64(10));
        assert_eq!(result.x, I1024::ONE);
    }

    #[test]
    fn test_extended_gcd_same_numbers() {
        let a = U1024::from_u64(42);
        let b = U1024::from_u64(42);
        let result = extended_gcd(a, b);
        assert_eq!(result.gcd, U1024::from_u64(42));
    }

    #[test]
    fn test_extended_gcd_large_numbers() {
        let a = U1024::from_u64(1071);
        let b = U1024::from_u64(462);
        let result = extended_gcd(a, b);
        assert_eq!(result.gcd, U1024::from_u64(21));
    }

    #[test]
    fn test_mod_inverse_basic() {
        let result = mod_inverse(U1024::from_u64(3), U1024::from_u64(7));
        assert_eq!(result, Some(U1024::from_u64(5)));
    }

    #[test]
    fn test_mod_inverse_no_inverse() {
        let result = mod_inverse(U1024::from_u64(2), U1024::from_u64(4));
        assert_eq!(result, None);

        let result = mod_inverse(U1024::from_u64(6), U1024::from_u64(9));
        assert_eq!(result, None);
    }

    #[test]
    fn test_mod_inverse_coprime() {
        let inv = mod_inverse(U1024::from_u64(17), U1024::from_u64(101)).unwrap();
        // Verify: 17 * inv mod 101 == 1
        let (prod, _) = U1024::from_u64(17).const_mul(&inv);
        let remainder = prod % U1024::from_u64(101);
        assert_eq!(remainder, U1024::from_u64(1));
    }
}
