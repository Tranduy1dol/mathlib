use std::fmt;
use std::ops::{Add, Mul, Sub};

use crate::U1024;
use crate::field::montgomery::MontgomeryParams;
use crate::traits::BigInt;

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
    /// use mathlib::U1024;
    /// use mathlib::field::element::FieldElement;
    /// use mathlib::field::montgomery::MontgomeryParams;
    /// use mathlib::traits::BigInt;
    ///
    /// // `params` should be initialized for the desired modulus.
    /// let modulus = U1024::from_u64(17);
    /// let root = U1024::from_u64(2);
    /// let params = MontgomeryParams::new(modulus, root);
    /// let value = U1024::from_u64(42);
    /// let fe = FieldElement::new(value, &params);
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
    /// use mathlib::U1024;
    /// use mathlib::field::element::FieldElement;
    /// use mathlib::field::montgomery::MontgomeryParams;
    /// use mathlib::traits::BigInt;
    ///
    /// let modulus = U1024::from_u64(17);
    /// let params = MontgomeryParams::new(modulus, U1024::from_u64(2));
    /// let mont_val = U1024::from_u64(5);
    /// let fe = FieldElement::from_montgomery(mont_val, &params);
    /// assert_eq!(fe.value, mont_val);
    /// assert_eq!(fe.params as *const _, &params as *const _);
    /// ```
    pub fn from_montgomery(value: U1024, params: &'a MontgomeryParams) -> Self {
        Self { value, params }
    }

    /// Constructs the additive identity (zero) in Montgomery form for the provided parameters.
    ///
    /// # Examples
    ///
    /// ```
    /// use mathlib::U1024;
    /// use mathlib::field::element::FieldElement;
    /// use mathlib::field::montgomery::MontgomeryParams;
    /// use mathlib::traits::BigInt;
    ///
    /// let modulus = U1024::from_u64(17);
    /// let params = MontgomeryParams::new(modulus, U1024::from_u64(2));
    /// let z = FieldElement::zero(&params);
    /// assert_eq!(z.to_u1024(), U1024::zero());
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
    /// use mathlib::U1024;
    /// use mathlib::field::element::FieldElement;
    /// use mathlib::field::montgomery::MontgomeryParams;
    /// use mathlib::traits::BigInt;
    ///
    /// let modulus = U1024::from_u64(17);
    /// let params = MontgomeryParams::new(modulus, U1024::from_u64(2));
    /// let one = FieldElement::one(&params);
    /// assert_eq!(one.to_u1024(), U1024::one());
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
    /// use mathlib::U1024;
    /// use mathlib::field::element::FieldElement;
    /// use mathlib::field::montgomery::MontgomeryParams;
    /// use mathlib::traits::BigInt;
    ///
    /// let modulus = U1024::from_u64(17);
    /// let params = MontgomeryParams::new(modulus, U1024::from_u64(2));
    /// let elem = FieldElement::one(&params);
    /// let canonical: U1024 = elem.to_u1024();
    /// ```
    pub fn to_u1024(&self) -> U1024 {
        self.params.reduce(&self.value, &U1024::zero())
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
    /// use mathlib::U1024;
    /// use mathlib::field::element::FieldElement;
    /// use mathlib::field::montgomery::MontgomeryParams;
    /// use mathlib::traits::BigInt;
    ///
    /// let modulus = U1024::from_u64(17);
    /// let params = MontgomeryParams::new(modulus, U1024::from_u64(2));
    /// let a = FieldElement::zero(&params);
    /// let b = FieldElement::one(&params);
    /// let c = a + b;
    /// // (0 + 1) mod 17 = 1
    /// assert_eq!(c.to_u1024(), U1024::one());
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
    /// use mathlib::U1024;
    /// use mathlib::field::element::FieldElement;
    /// use mathlib::field::montgomery::MontgomeryParams;
    /// use mathlib::traits::BigInt;
    ///
    /// let modulus = U1024::from_u64(17);
    /// let params = MontgomeryParams::new(modulus, U1024::from_u64(2));
    /// let a = FieldElement::one(&params);
    /// let b = FieldElement::zero(&params);
    /// let c = a - b;
    /// assert_eq!(c.to_u1024(), U1024::one());
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
    /// use mathlib::U1024;
    /// use mathlib::field::element::FieldElement;
    /// use mathlib::field::montgomery::MontgomeryParams;
    /// use mathlib::traits::BigInt;
    ///
    /// let modulus = U1024::from_u64(17);
    /// let params = MontgomeryParams::new(modulus, U1024::from_u64(2));
    /// let a = FieldElement::one(&params);
    /// let b = FieldElement::one(&params);
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
    /// use mathlib::U1024;
    /// use mathlib::field::element::FieldElement;
    /// use mathlib::field::montgomery::MontgomeryParams;
    /// use mathlib::traits::BigInt;
    ///
    /// let modulus = U1024::from_u64(17);
    /// let params = MontgomeryParams::new(modulus, U1024::from_u64(2));
    /// let fe = FieldElement::one(&params);
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
    /// use mathlib::U1024;
    /// use mathlib::field::element::FieldElement;
    /// use mathlib::field::montgomery::MontgomeryParams;
    /// use mathlib::traits::BigInt;
    ///
    /// let modulus = U1024::from_u64(17);
    /// let params = MontgomeryParams::new(modulus, U1024::from_u64(2));
    /// let a = FieldElement::zero(&params);
    /// let b = FieldElement::zero(&params);
    /// assert_eq!(a, b);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}
impl<'a> Eq for FieldElement<'a> {}
