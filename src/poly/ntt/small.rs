//! Specialized small-modulus field elements for Kyber and Dilithium.
//!
//! These implementations use native 32-bit arithmetic with Barrett reduction,
//! which is much more efficient than the U1024 Montgomery reduction for small moduli.
//!
//! # Usage
//!
//! ```rust,ignore
//! use lumen_math::poly::ntt::small::{KyberFieldElement, DilithiumFieldElement};
//!
//! let a = KyberFieldElement::new(100);
//! let b = KyberFieldElement::new(200);
//! let c = a * b;  // Efficient modular multiplication
//! ```

use std::ops::{Add, Mul, Neg, Sub};

// =============================================================================
// Kyber Field Element (q = 3329)
// =============================================================================

/// Kyber modulus: q = 3329
pub const KYBER_Q: u32 = 3329;

/// Primitive 256th root of unity for Kyber: ζ = 17
pub const KYBER_ZETA: u32 = 17;

/// Barrett reduction constant for Kyber: floor(2^32 / q)
const KYBER_BARRETT: u64 = (1u64 << 32) / (KYBER_Q as u64);

/// Field element for Kyber (q = 3329).
///
/// Uses 16-bit storage with 32-bit intermediate arithmetic and Barrett reduction.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct KyberFieldElement(u16);

impl KyberFieldElement {
    /// Creates a new field element, reducing the input modulo q.
    #[inline]
    pub const fn new(value: u32) -> Self {
        Self((value % KYBER_Q) as u16)
    }

    /// Creates a field element from a raw value (must be < q).
    ///
    /// # Safety
    /// The caller must ensure `value < KYBER_Q`.
    #[inline]
    pub const fn from_raw(value: u16) -> Self {
        debug_assert!((value as u32) < KYBER_Q);
        Self(value)
    }

    /// Returns the raw value.
    #[inline]
    pub const fn value(self) -> u16 {
        self.0
    }

    /// Returns zero.
    #[inline]
    pub const fn zero() -> Self {
        Self(0)
    }

    /// Returns one.
    #[inline]
    pub const fn one() -> Self {
        Self(1)
    }

    /// Returns the primitive 256th root of unity ζ = 17.
    #[inline]
    pub const fn zeta() -> Self {
        Self(KYBER_ZETA as u16)
    }

    /// Checks if this element is zero.
    #[inline]
    pub const fn is_zero(self) -> bool {
        self.0 == 0
    }

    /// Barrett reduction: reduces a u32 value modulo q.
    #[inline]
    fn barrett_reduce(x: u32) -> u16 {
        // t = floor(x * BARRETT / 2^32) ≈ floor(x / q)
        let t = ((x as u64 * KYBER_BARRETT) >> 32) as u32;
        // r = x - t * q
        let mut r = x - t * KYBER_Q;
        // Final correction (r might be >= q)
        if r >= KYBER_Q {
            r -= KYBER_Q;
        }
        r as u16
    }

    /// Modular multiplication using Barrett reduction.
    #[inline]
    pub fn mul_mod(self, rhs: Self) -> Self {
        let product = (self.0 as u32) * (rhs.0 as u32);
        Self(Self::barrett_reduce(product))
    }

    /// Modular addition.
    #[inline]
    pub fn add_mod(self, rhs: Self) -> Self {
        let sum = (self.0 as u32) + (rhs.0 as u32);
        if sum >= KYBER_Q {
            Self((sum - KYBER_Q) as u16)
        } else {
            Self(sum as u16)
        }
    }

    /// Modular subtraction.
    #[inline]
    pub fn sub_mod(self, rhs: Self) -> Self {
        if self.0 >= rhs.0 {
            Self(self.0 - rhs.0)
        } else {
            Self((self.0 as u32 + KYBER_Q - rhs.0 as u32) as u16)
        }
    }

    /// Modular negation.
    #[inline]
    pub fn neg_mod(self) -> Self {
        if self.0 == 0 {
            Self(0)
        } else {
            Self((KYBER_Q - self.0 as u32) as u16)
        }
    }

    /// Modular exponentiation using square-and-multiply.
    pub fn pow(self, mut exp: u32) -> Self {
        let mut result = Self::one();
        let mut base = self;
        while exp > 0 {
            if exp & 1 == 1 {
                result = result.mul_mod(base);
            }
            base = base.mul_mod(base);
            exp >>= 1;
        }
        result
    }

    /// Modular inverse using Fermat's little theorem: a^(-1) = a^(q-2) mod q.
    #[inline]
    pub fn inv(self) -> Self {
        self.pow(KYBER_Q - 2)
    }

    /// Convert to U1024 for compatibility testing.
    #[inline]
    pub fn to_u1024(self) -> crate::U1024 {
        crate::U1024::from_u64(self.0 as u64)
    }
}

// Operator implementations for KyberFieldElement
impl Add for KyberFieldElement {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        self.add_mod(rhs)
    }
}

impl Sub for KyberFieldElement {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        self.sub_mod(rhs)
    }
}

impl Mul for KyberFieldElement {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        self.mul_mod(rhs)
    }
}

impl Neg for KyberFieldElement {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        self.neg_mod()
    }
}

// =============================================================================
// Dilithium Field Element (q = 8380417)
// =============================================================================

/// Dilithium modulus: q = 8380417
pub const DILITHIUM_Q: u32 = 8380417;

/// Primitive 512th root of unity for Dilithium: ψ = 1753
pub const DILITHIUM_PSI: u32 = 1753;

/// Primitive 256th root of unity for Dilithium: ω = ψ² = 3073009
pub const DILITHIUM_OMEGA: u32 = 3073009;

/// Barrett reduction constant for Dilithium: floor(2^48 / q)
/// Using 48 bits to handle u32 * u32 products safely.
const DILITHIUM_BARRETT: u64 = (1u64 << 48) / (DILITHIUM_Q as u64);

/// Field element for Dilithium (q = 8380417).
///
/// Uses 32-bit storage with 64-bit intermediate arithmetic and Barrett reduction.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct DilithiumFieldElement(u32);

impl DilithiumFieldElement {
    /// Creates a new field element, reducing the input modulo q.
    #[inline]
    pub const fn new(value: u32) -> Self {
        Self(value % DILITHIUM_Q)
    }

    /// Creates a new field element from a u64, reducing modulo q.
    #[inline]
    pub fn from_u64(value: u64) -> Self {
        Self((value % (DILITHIUM_Q as u64)) as u32)
    }

    /// Creates a field element from a raw value (must be < q).
    ///
    /// # Safety
    /// The caller must ensure `value < DILITHIUM_Q`.
    #[inline]
    pub const fn from_raw(value: u32) -> Self {
        debug_assert!(value < DILITHIUM_Q);
        Self(value)
    }

    /// Returns the raw value.
    #[inline]
    pub const fn value(self) -> u32 {
        self.0
    }

    /// Returns zero.
    #[inline]
    pub const fn zero() -> Self {
        Self(0)
    }

    /// Returns one.
    #[inline]
    pub const fn one() -> Self {
        Self(1)
    }

    /// Returns the primitive 512th root of unity ψ = 1753.
    #[inline]
    pub const fn psi() -> Self {
        Self(DILITHIUM_PSI)
    }

    /// Returns the primitive 256th root of unity ω = 3073009.
    #[inline]
    pub const fn omega() -> Self {
        Self(DILITHIUM_OMEGA)
    }

    /// Checks if this element is zero.
    #[inline]
    pub const fn is_zero(self) -> bool {
        self.0 == 0
    }

    /// Barrett reduction: reduces a u64 value modulo q.
    #[inline]
    fn barrett_reduce(x: u64) -> u32 {
        // t = floor(x * BARRETT / 2^48) ≈ floor(x / q)
        let t = ((x as u128 * DILITHIUM_BARRETT as u128) >> 48) as u64;
        // r = x - t * q
        let mut r = x - t * (DILITHIUM_Q as u64);
        // Final correction (r might be >= q)
        while r >= DILITHIUM_Q as u64 {
            r -= DILITHIUM_Q as u64;
        }
        r as u32
    }

    /// Modular multiplication using Barrett reduction.
    #[inline]
    pub fn mul_mod(self, rhs: Self) -> Self {
        let product = (self.0 as u64) * (rhs.0 as u64);
        Self(Self::barrett_reduce(product))
    }

    /// Modular addition.
    #[inline]
    pub fn add_mod(self, rhs: Self) -> Self {
        let sum = (self.0 as u64) + (rhs.0 as u64);
        if sum >= DILITHIUM_Q as u64 {
            Self((sum - DILITHIUM_Q as u64) as u32)
        } else {
            Self(sum as u32)
        }
    }

    /// Modular subtraction.
    #[inline]
    pub fn sub_mod(self, rhs: Self) -> Self {
        if self.0 >= rhs.0 {
            Self(self.0 - rhs.0)
        } else {
            Self((self.0 as u64 + DILITHIUM_Q as u64 - rhs.0 as u64) as u32)
        }
    }

    /// Modular negation.
    #[inline]
    pub fn neg_mod(self) -> Self {
        if self.0 == 0 {
            Self(0)
        } else {
            Self(DILITHIUM_Q - self.0)
        }
    }

    /// Modular exponentiation using square-and-multiply.
    pub fn pow(self, mut exp: u32) -> Self {
        let mut result = Self::one();
        let mut base = self;
        while exp > 0 {
            if exp & 1 == 1 {
                result = result.mul_mod(base);
            }
            base = base.mul_mod(base);
            exp >>= 1;
        }
        result
    }

    /// Modular inverse using Fermat's little theorem: a^(-1) = a^(q-2) mod q.
    #[inline]
    pub fn inv(self) -> Self {
        self.pow(DILITHIUM_Q - 2)
    }

    /// Convert to U1024 for compatibility testing.
    #[inline]
    pub fn to_u1024(self) -> crate::U1024 {
        crate::U1024::from_u64(self.0 as u64)
    }
}

// Operator implementations for DilithiumFieldElement
impl Add for DilithiumFieldElement {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        self.add_mod(rhs)
    }
}

impl Sub for DilithiumFieldElement {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        self.sub_mod(rhs)
    }
}

impl Mul for DilithiumFieldElement {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        self.mul_mod(rhs)
    }
}

impl Neg for DilithiumFieldElement {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        self.neg_mod()
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // --- Kyber Tests ---

    #[test]
    fn test_kyber_basic_arithmetic() {
        let a = KyberFieldElement::new(1000);
        let b = KyberFieldElement::new(2000);

        // Addition
        let sum = a + b;
        assert_eq!(sum.value(), 3000);

        // Addition with wrap
        let c = KyberFieldElement::new(3000);
        let sum2 = c + c;
        assert_eq!(sum2.value(), (6000 % KYBER_Q) as u16);

        // Multiplication
        let prod = a * b;
        assert_eq!(prod.value(), ((1000u32 * 2000) % KYBER_Q) as u16);
    }

    #[test]
    fn test_kyber_primitive_root() {
        // Verify ζ^256 ≡ 1 (mod 3329)
        let zeta = KyberFieldElement::zeta();
        let result = zeta.pow(256);
        assert_eq!(result.value(), 1, "ζ^256 should equal 1 mod 3329");
    }

    #[test]
    fn test_kyber_primitive_root_half() {
        // Verify ζ^128 ≡ -1 (mod 3329)
        let zeta = KyberFieldElement::zeta();
        let result = zeta.pow(128);
        assert_eq!(
            result.value(),
            (KYBER_Q - 1) as u16,
            "ζ^128 should equal -1 mod 3329"
        );
    }

    #[test]
    fn test_kyber_inverse() {
        let a = KyberFieldElement::new(17);
        let a_inv = a.inv();
        let product = a * a_inv;
        assert_eq!(product.value(), 1, "a * a^(-1) should equal 1");
    }

    // --- Dilithium Tests ---

    #[test]
    fn test_dilithium_basic_arithmetic() {
        let a = DilithiumFieldElement::new(1000000);
        let b = DilithiumFieldElement::new(2000000);

        // Addition
        let sum = a + b;
        assert_eq!(sum.value(), 3000000);

        // Multiplication
        let prod = a * b;
        let expected = ((1000000u64 * 2000000) % (DILITHIUM_Q as u64)) as u32;
        assert_eq!(prod.value(), expected);
    }

    #[test]
    fn test_dilithium_primitive_2nth_root() {
        // Verify ψ^256 ≡ -1 (mod 8380417)
        let psi = DilithiumFieldElement::psi();
        let result = psi.pow(256);
        assert_eq!(
            result.value(),
            DILITHIUM_Q - 1,
            "ψ^256 should equal -1 mod 8380417"
        );
    }

    #[test]
    fn test_dilithium_primitive_nth_root() {
        // Verify ω^256 ≡ 1 (mod 8380417) where ω = ψ²
        let omega = DilithiumFieldElement::omega();
        let result = omega.pow(256);
        assert_eq!(result.value(), 1, "ω^256 should equal 1 mod 8380417");
    }

    #[test]
    fn test_dilithium_psi_squared_is_omega() {
        // Verify ψ² = ω
        let psi = DilithiumFieldElement::psi();
        let omega = DilithiumFieldElement::omega();
        let psi_squared = psi * psi;
        assert_eq!(psi_squared, omega, "ψ² should equal ω");
    }

    #[test]
    fn test_dilithium_inverse() {
        let a = DilithiumFieldElement::new(1753);
        let a_inv = a.inv();
        let product = a * a_inv;
        assert_eq!(product.value(), 1, "a * a^(-1) should equal 1");
    }
}
