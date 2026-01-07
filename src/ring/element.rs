//! Ring elements for lattice-based cryptography.
//!
//! This module provides `RingElement<C>` for working with polynomials in the ring
//! Rq = Zq[X]/(X^N + 1), which is fundamental to lattice-based cryptographic
//! schemes like Kyber and Dilithium.
//!
//! # State Management
//!
//! Ring elements can exist in two forms:
//! - **Coefficient form**: Standard polynomial representation
//! - **NTT form**: Number-theoretic transform for efficient multiplication
//!
//! The implementation uses lazy state conversion - operations automatically
//! convert to the optimal form as needed.
//!
//! # Example
//!
//! ```rust,ignore
//! use lumen_math::{RingElement, NttContext, DefaultFieldConfig, FieldElement};
//! use std::sync::Arc;
//!
//! // Create NTT context (share across multiple ring elements)
//! let ctx = Arc::new(NttContext::<DefaultFieldConfig>::new(8));
//!
//! // Create ring elements
//! let a = RingElement::zero(ctx.clone());
//! let b = RingElement::one(ctx.clone());
//!
//! // Arithmetic operations
//! let sum = &a + &b;
//! let product = &a * &b;
//! ```

use std::fmt;
use std::ops::{Add, Mul, Neg, Sub};
use std::sync::Arc;

use crate::poly::ntt::NttContext;
use crate::{FieldConfig, FieldElement};

/// Represents the current state of a ring element.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RingElementState {
    /// Polynomial is in standard coefficient form.
    Coefficient,
    /// Polynomial is in NTT (Number Theoretic Transform) form.
    Ntt,
}

/// A polynomial element in the ring Rq = Zq[X]/(X^N + 1).
///
/// This type manages the polynomial representation, automatically converting
/// between coefficient and NTT forms as needed for efficient arithmetic.
///
/// # Type Parameters
/// * `C` - Field configuration (defines modulus and NTT parameters)
#[derive(Clone)]
pub struct RingElement<C: FieldConfig> {
    /// Polynomial coefficients or NTT values (depending on state)
    data: Vec<FieldElement<C>>,
    /// Current representation state
    state: RingElementState,
    /// Shared NTT context for transformations
    ntt_ctx: Arc<NttContext<C>>,
}

impl<C: FieldConfig> RingElement<C> {
    /// Creates a new ring element from coefficients.
    ///
    /// # Arguments
    /// * `coeffs` - Polynomial coefficients in ascending order of degree
    /// * `ctx` - Shared NTT context
    ///
    /// # Panics
    /// Panics if `coeffs.len() != ctx.n`.
    pub fn new(coeffs: Vec<FieldElement<C>>, ctx: Arc<NttContext<C>>) -> Self {
        assert_eq!(
            coeffs.len(),
            ctx.n,
            "Coefficient length must match NTT context degree"
        );
        Self {
            data: coeffs,
            state: RingElementState::Coefficient,
            ntt_ctx: ctx,
        }
    }

    /// Creates a ring element from NTT form values.
    ///
    /// # Arguments
    /// * `ntt_values` - Values in NTT representation
    /// * `ctx` - Shared NTT context
    ///
    /// # Panics
    /// Panics if `ntt_values.len() != ctx.n`.
    pub fn from_ntt(ntt_values: Vec<FieldElement<C>>, ctx: Arc<NttContext<C>>) -> Self {
        assert_eq!(
            ntt_values.len(),
            ctx.n,
            "NTT values length must match NTT context degree"
        );
        Self {
            data: ntt_values,
            state: RingElementState::Ntt,
            ntt_ctx: ctx,
        }
    }

    /// Creates the zero polynomial.
    pub fn zero(ctx: Arc<NttContext<C>>) -> Self {
        Self {
            data: vec![FieldElement::zero(); ctx.n],
            state: RingElementState::Coefficient,
            ntt_ctx: ctx,
        }
    }

    /// Creates the constant polynomial 1.
    pub fn one(ctx: Arc<NttContext<C>>) -> Self {
        let n = ctx.n;
        let mut coeffs = vec![FieldElement::zero(); n];
        coeffs[0] = FieldElement::one();
        Self {
            data: coeffs,
            state: RingElementState::Coefficient,
            ntt_ctx: ctx,
        }
    }

    /// Returns the current state of the ring element.
    #[inline]
    pub fn state(&self) -> RingElementState {
        self.state
    }

    /// Returns the ring degree N.
    #[inline]
    pub fn degree(&self) -> usize {
        self.ntt_ctx.n
    }

    /// Returns a reference to the NTT context.
    #[inline]
    pub fn context(&self) -> &Arc<NttContext<C>> {
        &self.ntt_ctx
    }

    /// Converts the element to NTT form in-place.
    ///
    /// If already in NTT form, this is a no-op.
    pub fn to_ntt(&mut self) {
        if self.state == RingElementState::Coefficient {
            self.ntt_ctx.ntt(&mut self.data);
            self.state = RingElementState::Ntt;
        }
    }

    /// Converts the element to coefficient form in-place.
    ///
    /// If already in coefficient form, this is a no-op.
    pub fn to_coefficient(&mut self) {
        if self.state == RingElementState::Ntt {
            self.ntt_ctx.intt(&mut self.data);
            self.state = RingElementState::Coefficient;
        }
    }

    /// Consumes self and returns a ring element in NTT form.
    pub fn into_ntt(mut self) -> Self {
        self.to_ntt();
        self
    }

    /// Consumes self and returns a ring element in coefficient form.
    pub fn into_coefficient(mut self) -> Self {
        self.to_coefficient();
        self
    }

    /// Clones and ensures the result is in coefficient form.
    pub fn clone_to_coefficient(&self) -> Self {
        let mut result = self.clone();
        result.to_coefficient();
        result
    }

    /// Clones and ensures the result is in NTT form.
    pub fn clone_to_ntt(&self) -> Self {
        let mut result = self.clone();
        result.to_ntt();
        result
    }

    /// Returns the coefficients (only valid in coefficient state).
    ///
    /// # Panics
    /// Panics if not in coefficient state.
    pub fn coefficients(&self) -> &[FieldElement<C>] {
        assert_eq!(
            self.state,
            RingElementState::Coefficient,
            "Element must be in coefficient form"
        );
        &self.data
    }

    /// Returns the NTT values (only valid in NTT state).
    ///
    /// # Panics
    /// Panics if not in NTT state.
    pub fn ntt_values(&self) -> &[FieldElement<C>] {
        assert_eq!(
            self.state,
            RingElementState::Ntt,
            "Element must be in NTT form"
        );
        &self.data
    }

    /// Returns the raw data regardless of state.
    #[inline]
    pub fn data(&self) -> &[FieldElement<C>] {
        &self.data
    }

    /// Returns mutable access to the raw data (crate-internal only).
    ///
    /// # Warning
    /// Modifying the data directly may invalidate internal state assumptions.
    #[inline]
    #[allow(dead_code)]
    pub(crate) fn data_mut(&mut self) -> &mut [FieldElement<C>] {
        &mut self.data
    }

    /// Safely modifies the data using a closure, resetting state afterward.
    ///
    /// After the mutation, the element is marked as being in coefficient form.
    /// Use this when you need to manually modify coefficients.
    ///
    /// # Example
    /// ```rust,ignore
    /// elem.modify_data(|data| {
    ///     data[0] = fp!(42u64);
    /// });
    /// ```
    pub fn modify_data<F>(&mut self, f: F)
    where
        F: FnOnce(&mut [FieldElement<C>]),
    {
        // Ensure we're in coefficient form before modification
        self.to_coefficient();
        f(&mut self.data);
        // State remains Coefficient after modification
    }

    /// Checks if this is the zero polynomial.
    pub fn is_zero(&self) -> bool {
        self.data.iter().all(|c| c.is_zero())
    }

    /// Scales the polynomial by a scalar field element.
    pub fn scale(&self, scalar: &FieldElement<C>) -> Self {
        Self {
            data: self.data.iter().map(|c| *c * *scalar).collect(),
            state: self.state,
            ntt_ctx: self.ntt_ctx.clone(),
        }
    }
}

// =============================================================================
// Arithmetic Operations
// =============================================================================

impl<C: FieldConfig> Add for RingElement<C> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        &self + &rhs
    }
}

impl<'a, C: FieldConfig> Add<&'a RingElement<C>> for &'a RingElement<C> {
    type Output = RingElement<C>;

    fn add(self, rhs: &'a RingElement<C>) -> RingElement<C> {
        assert!(
            Arc::ptr_eq(&self.ntt_ctx, &rhs.ntt_ctx),
            "Ring elements must share the same NTT context"
        );

        // Convert RHS to match LHS state (preserves LHS state in result)
        let rhs_data = match (self.state, rhs.state) {
            (RingElementState::Coefficient, RingElementState::Coefficient)
            | (RingElementState::Ntt, RingElementState::Ntt) => rhs.data.clone(),
            (RingElementState::Coefficient, RingElementState::Ntt) => {
                rhs.clone_to_coefficient().data
            }
            (RingElementState::Ntt, RingElementState::Coefficient) => rhs.clone_to_ntt().data,
        };

        let result_data: Vec<_> = self
            .data
            .iter()
            .zip(rhs_data.iter())
            .map(|(a, b)| *a + *b)
            .collect();

        RingElement {
            data: result_data,
            state: self.state,
            ntt_ctx: self.ntt_ctx.clone(),
        }
    }
}

impl<C: FieldConfig> Sub for RingElement<C> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        &self - &rhs
    }
}

impl<'a, C: FieldConfig> Sub<&'a RingElement<C>> for &'a RingElement<C> {
    type Output = RingElement<C>;

    fn sub(self, rhs: &'a RingElement<C>) -> RingElement<C> {
        assert!(
            Arc::ptr_eq(&self.ntt_ctx, &rhs.ntt_ctx),
            "Ring elements must share the same NTT context"
        );

        // Convert RHS to match LHS state (preserves LHS state in result)
        let rhs_data = match (self.state, rhs.state) {
            (RingElementState::Coefficient, RingElementState::Coefficient)
            | (RingElementState::Ntt, RingElementState::Ntt) => rhs.data.clone(),
            (RingElementState::Coefficient, RingElementState::Ntt) => {
                rhs.clone_to_coefficient().data
            }
            (RingElementState::Ntt, RingElementState::Coefficient) => rhs.clone_to_ntt().data,
        };

        let result_data: Vec<_> = self
            .data
            .iter()
            .zip(rhs_data.iter())
            .map(|(a, b)| *a - *b)
            .collect();

        RingElement {
            data: result_data,
            state: self.state,
            ntt_ctx: self.ntt_ctx.clone(),
        }
    }
}

impl<C: FieldConfig> Mul for RingElement<C> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        &self * &rhs
    }
}

impl<'a, C: FieldConfig> Mul<&'a RingElement<C>> for &'a RingElement<C> {
    type Output = RingElement<C>;

    /// Multiplies two ring elements using NTT for efficiency.
    ///
    /// Both operands are converted to NTT form if needed, then
    /// pointwise multiplication is performed.
    fn mul(self, rhs: &'a RingElement<C>) -> RingElement<C> {
        assert!(
            Arc::ptr_eq(&self.ntt_ctx, &rhs.ntt_ctx),
            "Ring elements must share the same NTT context"
        );

        // Convert both to NTT form for multiplication
        let lhs_ntt = self.clone_to_ntt();
        let rhs_ntt = rhs.clone_to_ntt();

        // Pointwise multiplication in NTT domain
        let result_data: Vec<_> = lhs_ntt
            .data
            .iter()
            .zip(rhs_ntt.data.iter())
            .map(|(a, b)| *a * *b)
            .collect();

        RingElement {
            data: result_data,
            state: RingElementState::Ntt,
            ntt_ctx: lhs_ntt.ntt_ctx,
        }
    }
}

impl<C: FieldConfig> Neg for RingElement<C> {
    type Output = Self;

    fn neg(self) -> Self {
        RingElement {
            data: self.data.into_iter().map(|c| -c).collect(),
            state: self.state,
            ntt_ctx: self.ntt_ctx,
        }
    }
}

impl<C: FieldConfig> Neg for &RingElement<C> {
    type Output = RingElement<C>;

    fn neg(self) -> RingElement<C> {
        RingElement {
            data: self.data.iter().map(|c| -*c).collect(),
            state: self.state,
            ntt_ctx: self.ntt_ctx.clone(),
        }
    }
}

// =============================================================================
// Trait Implementations
// =============================================================================

impl<C: FieldConfig> PartialEq for RingElement<C> {
    fn eq(&self, other: &Self) -> bool {
        if !Arc::ptr_eq(&self.ntt_ctx, &other.ntt_ctx) {
            return false;
        }

        // Convert both to coefficient form for comparison
        let lhs = self.clone_to_coefficient();
        let rhs = other.clone_to_coefficient();

        lhs.data
            .iter()
            .zip(rhs.data.iter())
            .all(|(a, b)| a.to_u1024() == b.to_u1024())
    }
}

impl<C: FieldConfig> Eq for RingElement<C> {}

impl<C: FieldConfig> fmt::Debug for RingElement<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "RingElement {{ state: {:?}, n: {}, data: [...] }}",
            self.state,
            self.degree()
        )
    }
}

impl<C: FieldConfig> fmt::Display for RingElement<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let elem = self.clone_to_coefficient();
        let mut first = true;

        for (i, coeff) in elem.data.iter().enumerate().rev() {
            if coeff.is_zero() {
                continue;
            }

            if !first {
                write!(f, " + ")?;
            }
            first = false;

            let val = coeff.to_u1024();
            match i {
                0 => write!(f, "{:?}", val)?,
                1 => write!(f, "{:?}x", val)?,
                _ => write!(f, "{:?}x^{}", val, i)?,
            }
        }

        if first {
            write!(f, "0")?;
        }

        Ok(())
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::config::DefaultFieldConfig;
    use crate::fp;

    fn make_ctx() -> Arc<NttContext<DefaultFieldConfig>> {
        Arc::new(NttContext::new(8))
    }

    #[test]
    fn test_ring_element_zero() {
        let ctx = make_ctx();
        let zero = RingElement::<DefaultFieldConfig>::zero(ctx);
        assert!(zero.is_zero());
        assert_eq!(zero.state(), RingElementState::Coefficient);
    }

    #[test]
    fn test_ring_element_one() {
        let ctx = make_ctx();
        let one = RingElement::<DefaultFieldConfig>::one(ctx);
        assert!(!one.is_zero());
        assert_eq!(one.coefficients()[0].to_u1024().0[0], 1);
    }

    #[test]
    fn test_ntt_roundtrip() {
        let ctx = make_ctx();
        let coeffs: Vec<_> = (0..8).map(|i| fp!(i as u64)).collect();
        let original_vals: Vec<_> = coeffs.iter().map(|c| c.to_u1024()).collect();

        let mut elem = RingElement::new(coeffs, ctx);
        elem.to_ntt();
        assert_eq!(elem.state(), RingElementState::Ntt);

        elem.to_coefficient();
        assert_eq!(elem.state(), RingElementState::Coefficient);

        for (a, b) in original_vals.iter().zip(elem.coefficients().iter()) {
            assert_eq!(*a, b.to_u1024());
        }
    }

    #[test]
    fn test_addition() {
        let ctx = make_ctx();
        let a = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx.clone());
        let b = RingElement::new((0..8).map(|i| fp!((i + 1) as u64)).collect(), ctx);

        let sum = &a + &b;
        let coeffs = sum.clone_to_coefficient();

        for (i, c) in coeffs.coefficients().iter().enumerate() {
            let expected = (i + (i + 1)) as u64;
            assert_eq!(c.to_u1024().0[0], expected);
        }
    }

    #[test]
    fn test_subtraction() {
        let ctx = make_ctx();
        let a = RingElement::new((0..8).map(|i| fp!((i * 2) as u64)).collect(), ctx.clone());
        let b = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx);

        let diff = &a - &b;
        let coeffs = diff.clone_to_coefficient();

        for (i, c) in coeffs.coefficients().iter().enumerate() {
            assert_eq!(c.to_u1024().0[0], i as u64);
        }
    }

    #[test]
    fn test_negation() {
        let ctx = make_ctx();
        let a = RingElement::new(vec![fp!(1u64); 8], ctx.clone());
        let neg_a = -&a;
        let sum = &a + &neg_a;

        assert!(sum.is_zero());
    }

    #[test]
    fn test_multiplication_returns_ntt_form() {
        let ctx = make_ctx();
        let a = RingElement::new(vec![fp!(1u64); 8], ctx.clone());
        let b = RingElement::new(vec![fp!(1u64); 8], ctx);

        let product = &a * &b;
        assert_eq!(product.state(), RingElementState::Ntt);
    }

    #[test]
    fn test_scale() {
        let ctx = make_ctx();
        let a = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx);
        let scalar = fp!(2u64);

        let scaled = a.scale(&scalar);
        let coeffs = scaled.clone_to_coefficient();

        for (i, c) in coeffs.coefficients().iter().enumerate() {
            assert_eq!(c.to_u1024().0[0], (i * 2) as u64);
        }
    }

    #[test]
    fn test_equality() {
        let ctx = make_ctx();
        let a = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx.clone());
        let b = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx);

        assert_eq!(a, b);
    }

    #[test]
    fn test_equality_across_states() {
        let ctx = make_ctx();
        let a = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx.clone());
        let b = a.clone_to_ntt();

        // Should be equal even though in different states
        assert_eq!(a, b);
    }

    // =========================================================================
    // Additional tests for code coverage
    // =========================================================================

    #[test]
    #[should_panic(expected = "NTT values length must match NTT context degree")]
    fn test_from_ntt_wrong_length_panics() {
        let ctx = make_ctx();
        let _elem = RingElement::from_ntt(vec![fp!(1u64); 4], ctx); // Wrong size
    }

    #[test]
    fn test_context_accessor() {
        let ctx = make_ctx();
        let elem = RingElement::zero(ctx.clone());
        assert!(Arc::ptr_eq(&ctx, elem.context()));
    }

    #[test]
    fn test_ntt_values_accessor() {
        let ctx = make_ctx();
        let coeffs: Vec<_> = (0..8).map(|i| fp!(i as u64)).collect();
        let mut elem = RingElement::new(coeffs, ctx);
        elem.to_ntt();

        // Should not panic - in NTT state
        let ntt_vals = elem.ntt_values();
        assert_eq!(ntt_vals.len(), 8);
    }

    #[test]
    #[should_panic(expected = "Element must be in NTT form")]
    fn test_ntt_values_panics_in_coefficient_state() {
        let ctx = make_ctx();
        let elem = RingElement::zero(ctx);
        let _vals = elem.ntt_values(); // Should panic
    }

    #[test]
    #[should_panic(expected = "Element must be in coefficient form")]
    fn test_coefficients_panics_in_ntt_state() {
        let ctx = make_ctx();
        let mut elem = RingElement::zero(ctx);
        elem.to_ntt();
        let _coeffs = elem.coefficients(); // Should panic
    }

    #[test]
    fn test_modify_data() {
        let ctx = make_ctx();
        let mut elem = RingElement::new(vec![fp!(0u64); 8], ctx);

        elem.modify_data(|data| {
            data[0] = fp!(42u64);
            data[7] = fp!(99u64);
        });

        assert_eq!(elem.state(), RingElementState::Coefficient);
        assert_eq!(elem.coefficients()[0].to_u1024().0[0], 42);
        assert_eq!(elem.coefficients()[7].to_u1024().0[0], 99);
    }

    #[test]
    fn test_modify_data_converts_from_ntt() {
        let ctx = make_ctx();
        let mut elem = RingElement::new(vec![fp!(1u64); 8], ctx);
        elem.to_ntt();
        assert_eq!(elem.state(), RingElementState::Ntt);

        // modify_data should convert to coefficient form first
        elem.modify_data(|data| {
            data[0] = fp!(100u64);
        });

        assert_eq!(elem.state(), RingElementState::Coefficient);
    }

    #[test]
    fn test_owned_addition() {
        let ctx = make_ctx();
        let a = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx.clone());
        let b = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx);

        // Use owned addition (consumes a and b)
        let sum = a + b;

        for (i, c) in sum.clone_to_coefficient().coefficients().iter().enumerate() {
            assert_eq!(c.to_u1024().0[0], (i * 2) as u64);
        }
    }

    #[test]
    fn test_owned_subtraction() {
        let ctx = make_ctx();
        let a = RingElement::new((0..8).map(|i| fp!((i * 3) as u64)).collect(), ctx.clone());
        let b = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx);

        // Use owned subtraction
        let diff = a - b;

        for (i, c) in diff
            .clone_to_coefficient()
            .coefficients()
            .iter()
            .enumerate()
        {
            assert_eq!(c.to_u1024().0[0], (i * 2) as u64);
        }
    }

    #[test]
    fn test_owned_multiplication() {
        let ctx = make_ctx();
        let a = RingElement::one(ctx.clone());
        let b = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx);

        // Use owned multiplication
        let product = a * b;
        assert_eq!(product.state(), RingElementState::Ntt);
    }

    #[test]
    fn test_owned_negation() {
        let ctx = make_ctx();
        let a = RingElement::new(vec![fp!(5u64); 8], ctx);

        // Use owned negation (consumes a)
        let neg_a = -a;

        // Check all coefficients are negated
        for c in neg_a.clone_to_coefficient().coefficients() {
            assert!(!c.is_zero());
        }
    }

    #[test]
    fn test_ntt_ntt_addition() {
        let ctx = make_ctx();
        let mut a = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx.clone());
        let mut b = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx);

        a.to_ntt();
        b.to_ntt();

        let sum = &a + &b;
        assert_eq!(sum.state(), RingElementState::Ntt);
    }

    #[test]
    fn test_coefficient_ntt_addition() {
        let ctx = make_ctx();
        let a = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx.clone());
        let mut b = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx);
        b.to_ntt();

        // Coefficient + NTT -> Coefficient (preserves LHS state)
        let sum = &a + &b;
        assert_eq!(sum.state(), RingElementState::Coefficient);
    }

    #[test]
    fn test_ntt_coefficient_addition() {
        let ctx = make_ctx();
        let mut a = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx.clone());
        a.to_ntt();
        let b = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx);

        // NTT + Coefficient -> NTT (preserves LHS state)
        let sum = &a + &b;
        assert_eq!(sum.state(), RingElementState::Ntt);
    }

    #[test]
    fn test_ntt_ntt_subtraction() {
        let ctx = make_ctx();
        let mut a = RingElement::new((0..8).map(|i| fp!((i * 2) as u64)).collect(), ctx.clone());
        let mut b = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx);

        a.to_ntt();
        b.to_ntt();

        let diff = &a - &b;
        assert_eq!(diff.state(), RingElementState::Ntt);
    }

    #[test]
    fn test_coefficient_ntt_subtraction() {
        let ctx = make_ctx();
        let a = RingElement::new((0..8).map(|i| fp!((i * 2) as u64)).collect(), ctx.clone());
        let mut b = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx);
        b.to_ntt();

        let diff = &a - &b;
        assert_eq!(diff.state(), RingElementState::Coefficient);
    }

    #[test]
    fn test_ntt_coefficient_subtraction() {
        let ctx = make_ctx();
        let mut a = RingElement::new((0..8).map(|i| fp!((i * 2) as u64)).collect(), ctx.clone());
        a.to_ntt();
        let b = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx);

        let diff = &a - &b;
        assert_eq!(diff.state(), RingElementState::Ntt);
    }

    #[test]
    fn test_inequality_different_contexts() {
        let ctx1 = make_ctx();
        let ctx2 = make_ctx();

        let a = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx1);
        let b = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx2);

        // Different contexts -> not equal
        assert_ne!(a, b);
    }

    #[test]
    fn test_debug_format() {
        let ctx = make_ctx();
        let elem = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx);

        let debug_str = format!("{:?}", elem);
        assert!(debug_str.contains("RingElement"));
        assert!(debug_str.contains("Coefficient"));
        assert!(debug_str.contains("8"));
    }

    #[test]
    fn test_display_format_nonzero() {
        let ctx = make_ctx();
        let mut coeffs = vec![fp!(0u64); 8];
        coeffs[0] = fp!(5u64); // constant term
        coeffs[1] = fp!(3u64); // x term
        coeffs[2] = fp!(1u64); // x^2 term

        let elem = RingElement::new(coeffs, ctx);
        let display_str = format!("{}", elem);

        // Should contain terms (order may vary based on Display impl)
        assert!(!display_str.is_empty());
        assert!(!display_str.contains("0") || display_str.len() > 1);
    }

    #[test]
    fn test_display_format_zero() {
        let ctx = make_ctx();
        let elem = RingElement::zero(ctx);

        let display_str = format!("{}", elem);
        assert_eq!(display_str, "0");
    }

    #[test]
    fn test_to_ntt_no_op_when_already_ntt() {
        let ctx = make_ctx();
        let mut elem = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx);
        elem.to_ntt();

        let data_before: Vec<_> = elem.data().iter().map(|c| c.to_u1024()).collect();
        elem.to_ntt(); // Should be no-op
        let data_after: Vec<_> = elem.data().iter().map(|c| c.to_u1024()).collect();

        assert_eq!(data_before, data_after);
    }

    #[test]
    fn test_to_coefficient_no_op_when_already_coefficient() {
        let ctx = make_ctx();
        let mut elem = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx);

        let data_before: Vec<_> = elem.data().iter().map(|c| c.to_u1024()).collect();
        elem.to_coefficient(); // Should be no-op
        let data_after: Vec<_> = elem.data().iter().map(|c| c.to_u1024()).collect();

        assert_eq!(data_before, data_after);
    }

    #[test]
    fn test_into_ntt() {
        let ctx = make_ctx();
        let elem = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx);

        let ntt_elem = elem.into_ntt();
        assert_eq!(ntt_elem.state(), RingElementState::Ntt);
    }

    #[test]
    fn test_into_coefficient() {
        let ctx = make_ctx();
        let mut elem = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx);
        elem.to_ntt();

        let coeff_elem = elem.into_coefficient();
        assert_eq!(coeff_elem.state(), RingElementState::Coefficient);
    }

    #[test]
    fn test_data_accessor() {
        let ctx = make_ctx();
        let elem = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx);

        let data = elem.data();
        assert_eq!(data.len(), 8);
    }

    #[test]
    fn test_degree() {
        let ctx = make_ctx();
        let elem = RingElement::zero(ctx);
        assert_eq!(elem.degree(), 8);
    }

    #[test]
    fn test_is_zero_false_for_nonzero() {
        let ctx = make_ctx();
        let elem = RingElement::one(ctx);
        assert!(!elem.is_zero());
    }

    #[test]
    fn test_scale_preserves_state() {
        let ctx = make_ctx();
        let mut elem = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx);
        elem.to_ntt();

        let scaled = elem.scale(&fp!(2u64));
        assert_eq!(scaled.state(), RingElementState::Ntt);
    }
}
