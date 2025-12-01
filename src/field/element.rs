use std::fmt;
use std::ops::{Add, Mul, Sub};

use crate::U1024;
use crate::field::montgomery::MontgomeryParams;
use crate::traits::BigInt;

#[derive(Clone)]
pub struct FieldElement<'a> {
    pub value: U1024,
    pub params: &'a MontgomeryParams,
}

impl<'a> FieldElement<'a> {
    /// Constructs a FieldElement by converting a standard integer into Montgomery form.
    ///
    /// The provided `value` is mapped into the field's Montgomery representation using the
    /// supplied Montgomery parameters so the returned element is ready for Montgomery arithmetic.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use crate::field::{FieldElement, MontgomeryParams};
    /// # use crate::u1024::U1024;
    /// // `params` should be initialized for the desired modulus.
    /// let params: MontgomeryParams = /* initialize Montgomery parameters */ todo!();
    /// let value = U1024::from(42u64);
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
    /// // `mont_val` is a U1024 holding a Montgomery-form value and `params` are MontgomeryParams.
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
    /// // `params` is a `&MontgomeryParams` available in scope.
    /// let z = FieldElement::zero(params);
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
    /// // `params` should be a valid `MontgomeryParams` for the field.
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
    /// ```no_run
    /// # use crate::{FieldElement, MontgomeryParams, U1024};
    /// // `params` must be constructed for the field before use.
    /// let params: MontgomeryParams = /* ... */ unimplemented!();
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
    /// // assuming `params` and `U1024` are available in scope
    /// let a = FieldElement::zero(&params);
    /// let b = FieldElement::one(&params);
    /// let c = a + b;
    /// assert_eq!(c.to_u1024(), (a.to_u1024() + b.to_u1024()) % params.modulus);
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
    /// // given `a`, `b` of type `FieldElement` with the same `params`
    /// let c = a - b;
    /// // `c` is the Montgomery-form representation of (a - b) mod modulus
    /// assert_eq!(c.to_u1024(), {
    ///     // canonical check: convert operands out of Montgomery form, do integer subtraction modulo modulus
    ///     let av = a.to_u1024();
    ///     let bv = b.to_u1024();
    ///     let modulus = a.params.modulus;
    ///     let diff = if av >= bv { av - bv } else { av + modulus - bv };
    ///     diff
    /// });
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
    /// # use crate::field::element::FieldElement;
    /// # use crate::field::montgomery::MontgomeryParams;
    /// # // Setup (hidden): construct MontgomeryParams and two elements in Montgomery form.
    /// # let params = unsafe { MontgomeryParams::example() }; // example constructor hidden
    /// # let a = FieldElement::one(&params);
    /// # let b = FieldElement::one(&params);
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
    /// ```no_run
    /// // Given a `FieldElement` `fe`, the debug output includes the canonical value.
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
    /// // Construct two field elements with the same Montgomery representation.
    /// let params = /* MontgomeryParams for the field */;
    /// let a = FieldElement::zero(&params);
    /// let b = FieldElement::zero(&params);
    /// assert_eq!(a, b);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}
impl<'a> Eq for FieldElement<'a> {}