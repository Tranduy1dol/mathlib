use std::fmt;
use std::ops::{Add, Mul, Sub};

use crate::U1024;
use crate::field::montgomery::MontgomeryParams;
use crate::traits::BigInt;

/// Macro to create a FieldElement from different sources.
///
/// # Examples
///
/// ```
/// use mathlib::{fp, mont, u1024};
///
/// let modulus = u1024!(17);
/// let params = mont!(modulus, u1024!(2));
///
/// // From hex string
/// let a = fp!("0x1234", &params);
///
/// // From primitive types
/// let b = fp!(42u8, &params);
/// let c = fp!(1000u16, &params);
/// let d = fp!(100000u32, &params);
/// let e = fp!(123456789u64, &params);
/// let f = fp!(0x123456789ABCDEFu128, &params);
///
/// // From U1024
/// let g = fp!(u1024!(5), &params);
/// ```
#[macro_export]
macro_rules! fp {
    // From array of u64
    ([$($limb:expr),+ $(,)?], $params:expr) => {{
        let u1024_val = $crate::U1024([$($limb),+]);
        $crate::field::element::FieldElement::new(u1024_val, $params)
    }};
    // From any other expression (hex string or numeric)
    ($val:expr, $params:expr) => {{
        #[allow(unused_imports)]
        {
            // Helper trait to convert to FieldElement
            trait ToFieldElement {
                fn to_field_element<'a>(self, params: &'a $crate::field::montgomery::MontgomeryParams) -> $crate::field::element::FieldElement<'a>;
            }

            impl ToFieldElement for &str {
                fn to_field_element<'a>(self, params: &'a $crate::field::montgomery::MontgomeryParams) -> $crate::field::element::FieldElement<'a> {
                    $crate::field::element::FieldElement::new($crate::U1024::from_hex(self), params)
                }
            }

            impl ToFieldElement for u8 {
                fn to_field_element<'a>(self, params: &'a $crate::field::montgomery::MontgomeryParams) -> $crate::field::element::FieldElement<'a> {
                    $crate::field::element::FieldElement::new($crate::U1024::from_u8(self), params)
                }
            }

            impl ToFieldElement for u16 {
                fn to_field_element<'a>(self, params: &'a $crate::field::montgomery::MontgomeryParams) -> $crate::field::element::FieldElement<'a> {
                    $crate::field::element::FieldElement::new($crate::U1024::from_u16(self), params)
                }
            }

            impl ToFieldElement for u32 {
                fn to_field_element<'a>(self, params: &'a $crate::field::montgomery::MontgomeryParams) -> $crate::field::element::FieldElement<'a> {
                    $crate::field::element::FieldElement::new($crate::U1024::from_u32(self), params)
                }
            }

            impl ToFieldElement for u64 {
                fn to_field_element<'a>(self, params: &'a $crate::field::montgomery::MontgomeryParams) -> $crate::field::element::FieldElement<'a> {
                    $crate::field::element::FieldElement::new($crate::U1024::from_u64(self), params)
                }
            }

            impl ToFieldElement for u128 {
                fn to_field_element<'a>(self, params: &'a $crate::field::montgomery::MontgomeryParams) -> $crate::field::element::FieldElement<'a> {
                    $crate::field::element::FieldElement::new($crate::U1024::from_u128(self), params)
                }
            }

            impl ToFieldElement for $crate::U1024 {
                fn to_field_element<'a>(self, params: &'a $crate::field::montgomery::MontgomeryParams) -> $crate::field::element::FieldElement<'a> {
                    $crate::field::element::FieldElement::new(self, params)
                }
            }

            ToFieldElement::to_field_element($val, $params)
        }
    }};
}

#[derive(Clone, Copy)]
pub struct FieldElement<'a> {
    pub value: U1024,
    pub params: &'a MontgomeryParams,
}

impl<'a> FieldElement<'a> {
    /// Constructs a FieldElement by converting a standard integer into a Montgomery form.
    ///
    /// The provided `value` is mapped into the field's Montgomery representation using the
    /// supplied Montgomery parameters, so the returned element is ready for Montgomery arithmetic.
    ///
    /// # Examples
    ///
    /// ```
    /// use mathlib::{fp, mont, u1024};
    ///
    /// // `params` should be initialized for the desired modulus.
    /// let modulus = u1024!(17);
    /// let root = u1024!(2);
    /// let params = mont!(modulus, root);
    /// let value = u1024!(42);
    /// let fe = fp!(value, &params);
    /// ```
    pub fn new(value: U1024, params: &'a MontgomeryParams) -> Self {
        let (lo, hi) = value.full_mul(&params.r2);
        let mont_value = params.reduce(&lo, &hi);

        Self {
            value: mont_value,
            params,
        }
    }

    /// Creates a FieldElement from an existing value already in Montgomery representation.
    ///
    /// The provided `value` is assumed to be in Montgomery form and is stored directly without
    /// further reduction or transformation. `params` supplies the Montgomery parameters that
    /// describe the modulus and reduction behavior associated with this value.
    ///
    /// # Examples
    ///
    /// ```
    /// use mathlib::{mont, u1024};
    /// use mathlib::field::element::FieldElement;
    ///
    /// let params = mont!(17u64, 2u64);
    /// let mont_val = u1024!(5u64);
    /// let fe = FieldElement::from_montgomery(mont_val, &params);
    /// assert_eq!(fe.value, mont_val);
    /// assert_eq!(fe.params as *const _, &params as *const _);
    /// ```
    pub fn from_montgomery(value: U1024, params: &'a MontgomeryParams) -> Self {
        // No conversion - value is yet in Montgomery form
        Self { value, params }
    }

    /// Constructs the additive identity (zero) in Montgomery form for the provided parameters.
    ///
    /// # Examples
    ///
    /// ```
    /// use mathlib::{mont, u1024};
    /// use mathlib::field::element::FieldElement;
    ///
    /// let params = mont!(17u64, 2u64);
    /// let z = FieldElement::zero(&params);
    /// assert_eq!(z.to_u1024(), u1024!(0u64));
    /// ```
    pub fn zero(params: &'a MontgomeryParams) -> Self {
        Self {
            value: U1024::zero(),
            params,
        }
    }

    /// Creates the multiplicative identity in Montgomery form.
    ///
    /// Returns a `FieldElement` whose internal `value` is the Montgomery-form representation of 1.
    ///
    /// # Examples
    ///
    /// ```
    /// use mathlib::{mont, u1024};
    /// use mathlib::field::element::FieldElement;
    ///
    /// let params = mont!(17u64, 2u64);
    /// let one = FieldElement::one(&params);
    /// assert_eq!(one.to_u1024(), u1024!(1u64));
    /// ```
    pub fn one(params: &'a MontgomeryParams) -> Self {
        Self::new(U1024::one(), params)
    }

    /// Convert this element from Montgomery form into its canonical U1024 representation.
    ///
    /// # Returns
    ///
    /// `U1024` containing the canonical (standard) representation of this field element.
    ///
    /// # Examples
    ///
    /// ```
    /// use mathlib::{fp, mont, U1024};
    /// use mathlib::field::element::FieldElement;
    ///
    /// let params = mont!(17u64, 2u64);
    /// let elem = fp!(1u64, &params);
    /// let canonical: U1024 = elem.to_u1024();
    /// ```
    pub fn to_u1024(&self) -> U1024 {
        self.params.reduce(&self.value, &U1024::zero())
    }

    /// Computes `self` raised to the power of `exp` using square-and-multiply.
    ///
    /// The exponent `exp` is a `U1024` integer. The result is returned in Montgomery form.
    ///
    /// # Examples
    ///
    /// ```
    /// use mathlib::{fp, mont, u1024};
    ///
    /// let params = mont!(17u64, 2u64);
    /// let base = fp!(3u64, &params);
    /// let exp = u1024!(3u64);
    /// let res = base.pow(exp);
    /// // 3^3 = 27 = 10 mod 17
    /// assert_eq!(res.to_u1024(), u1024!(10u64));
    /// ```
    pub fn pow(&self, exp: U1024) -> Self {
        let mut res = Self::one(self.params);
        let mut base = *self;

        for i in 0..16 {
            let mut limb = exp.0[i];
            for _ in 0..64 {
                if (limb & 1) == 1 {
                    res = res * base;
                }
                base = base * base;
                limb >>= 1;
            }
        }
        res
    }

    /// Computes the modular multiplicative inverse of `self`.
    ///
    /// This method uses Fermat's Little Theorem, computing `self^(modulus - 2)`.
    /// It assumes the modulus is prime. If `self` is zero, the result is effectively
    /// division by zero (undefined behavior in pure math), but here it will return
    /// `0^(p-2) = 0`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mathlib::{fp, mont, u1024};
    ///
    /// let params = mont!(17u64, 2u64);
    /// let a = fp!(3u64, &params);
    /// let inv = a.inv();
    /// // 3 * 6 = 18 = 1 mod 17
    /// assert_eq!((a * inv).to_u1024(), u1024!(1u64));
    /// ```
    pub fn inv(&self) -> Self {
        let two = U1024::from_u64(2);
        let (p_minus_2, _) = self.params.modulus.borrowing_sub(&two);
        self.pow(p_minus_2)
    }
}

impl<'a> Add for FieldElement<'a> {
    type Output = Self;
    /// Adds two field elements modulo the field modulus and returns the result in Montgomery form.
    ///
    /// The returned element represents (self + rhs) mod modulus, stored in the internal Montgomery representation.
    ///
    /// # Examples
    ///
    /// ```
    /// use mathlib::{fp, mont, u1024, BigInt};
    /// use mathlib::field::element::FieldElement;
    ///
    /// let params = mont!(17u64, 2u64);
    /// let a = fp!(0u64, &params);
    /// let b = fp!(1u64, &params);
    /// let c = a + b;
    /// // (0 + 1) mod 17 = 1
    /// assert_eq!(c.to_u1024(), u1024!(1u64));
    /// ```
    fn add(self, rhs: Self) -> Self {
        let (sum, carry) = self.value.carrying_add(&rhs.value);

        let (sub_res, borrow) = sum.borrowing_sub(&self.params.modulus);
        let use_sub = carry || !borrow;

        Self {
            value: U1024::conditional_select(&sub_res, &sum, use_sub),
            params: self.params,
        }
    }
}

impl<'a> Sub for FieldElement<'a> {
    type Output = Self;
    /// Subtracts another field element from this one and returns the difference in Montgomery form.
    ///
    /// The result is reduced modulo the field modulus and remains in Montgomery representation.
    /// If the raw subtraction underflows, the modulus is added to produce the correct non-negative residue.
    ///
    /// # Examples
    ///
    /// ```
    /// use mathlib::{fp, mont, u1024};
    /// use mathlib::field::element::FieldElement;
    ///
    /// let params = mont!(17u64, 2u64);
    /// let a = fp!(1u64, &params);
    /// let b = fp!(0u64, &params);
    /// let c = a - b;
    /// assert_eq!(c.to_u1024(), u1024!(1u64));
    /// ```
    fn sub(self, rhs: Self) -> Self {
        let (diff, borrow) = self.value.borrowing_sub(&rhs.value);

        let (corr, _) = diff.carrying_add(&self.params.modulus);
        Self {
            value: U1024::conditional_select(&corr, &diff, borrow),
            params: self.params,
        }
    }
}

impl<'a> Mul for FieldElement<'a> {
    type Output = Self;
    /// Multiplies two field elements and returns their product in Montgomery form.
    ///
    /// # Examples
    ///
    /// ```
    /// use mathlib::{fp, mont};
    /// use mathlib::field::element::FieldElement;
    ///
    /// let params = mont!(17u64, 2u64);
    /// let a = fp!(1u64, &params);
    /// let b = fp!(1u64, &params);
    /// let c = a * b;
    /// assert_eq!(c, FieldElement::one(&params));
    /// ```
    fn mul(self, rhs: Self) -> Self {
        let (lo, hi) = self.value.full_mul(&rhs.value);

        let res = self.params.reduce(&lo, &hi);

        Self {
            value: res,
            params: self.params,
        }
    }
}

impl<'a> fmt::Debug for FieldElement<'a> {
    /// Formats the field element for debugging as `FieldElement(<canonical value>)`.
    ///
    /// The displayed inner value is the canonical (non‑Montgomery) representation obtained
    /// from the element.
    ///
    /// # Examples
    ///
    /// ```
    /// use mathlib::{fp, mont};
    ///
    /// let params = mont!(17u64, 2u64);
    /// let fe = fp!(1u64, &params);
    /// let s = format!("{:?}", fe);
    /// assert!(s.starts_with("FieldElement("));
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let raw = self.to_u1024();
        write!(f, "FieldElement({:?})", raw)
    }
}

impl<'a> PartialEq for FieldElement<'a> {
    /// Compare two `FieldElement`s by their internal Montgomery representation.
    ///
    /// Returns `true` if the underlying Montgomery `value` fields are equal, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use mathlib::{fp, mont};
    ///
    /// let params = mont!(17u64, 2u64);
    /// let a = fp!(0u64, &params);
    /// let b = fp!(0u64, &params);
    /// assert_eq!(a, b);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}
impl<'a> Eq for FieldElement<'a> {}
