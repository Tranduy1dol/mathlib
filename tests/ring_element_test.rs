//! Integration tests for RingElement.

use std::sync::Arc;

use lumen_math::{
    FieldElement, NttContext, RingElement, RingElementState, field::config::DefaultFieldConfig, fp,
};

fn make_ctx() -> Arc<NttContext<DefaultFieldConfig>> {
    Arc::new(NttContext::new(8))
}

#[test]
fn test_ring_element_construction() {
    let ctx = make_ctx();

    let zero = RingElement::<DefaultFieldConfig>::zero(ctx.clone());
    assert!(zero.is_zero());
    assert_eq!(zero.state(), RingElementState::Coefficient);
    assert_eq!(zero.degree(), 8);

    let one = RingElement::<DefaultFieldConfig>::one(ctx);
    assert!(!one.is_zero());
}

#[test]
fn test_ntt_state_conversions() {
    let ctx = make_ctx();
    let coeffs: Vec<FieldElement<DefaultFieldConfig>> = (0..8).map(|i| fp!(i as u64)).collect();
    let original: Vec<_> = coeffs.iter().map(|c| c.to_u1024()).collect();

    let mut elem = RingElement::new(coeffs, ctx);

    // Convert to NTT
    elem.to_ntt();
    assert_eq!(elem.state(), RingElementState::Ntt);

    // Convert back to coefficient
    elem.to_coefficient();
    assert_eq!(elem.state(), RingElementState::Coefficient);

    // Verify values preserved
    for (i, c) in elem.coefficients().iter().enumerate() {
        assert_eq!(c.to_u1024(), original[i]);
    }
}

#[test]
fn test_into_conversions() {
    let ctx = make_ctx();
    let coeffs: Vec<FieldElement<DefaultFieldConfig>> = (0..8).map(|i| fp!(i as u64)).collect();

    let elem = RingElement::new(coeffs, ctx);
    let ntt_elem = elem.clone().into_ntt();
    assert_eq!(ntt_elem.state(), RingElementState::Ntt);

    let coeff_elem = ntt_elem.into_coefficient();
    assert_eq!(coeff_elem.state(), RingElementState::Coefficient);

    // Original and round-tripped should be equal
    assert_eq!(elem, coeff_elem);
}

#[test]
fn test_addition_preserves_state() {
    let ctx = make_ctx();
    let a = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx.clone());
    let b = RingElement::new((0..8).map(|i| fp!((i + 10) as u64)).collect(), ctx);

    let sum = &a + &b;
    assert_eq!(sum.state(), RingElementState::Coefficient);

    // Verify addition
    let coeffs = sum.coefficients();
    for i in 0..8 {
        let expected = (i + (i + 10)) as u64;
        assert_eq!(coeffs[i].to_u1024().0[0], expected);
    }
}

#[test]
fn test_subtraction() {
    let ctx = make_ctx();
    let a = RingElement::new((0..8).map(|i| fp!((i * 3) as u64)).collect(), ctx.clone());
    let b = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx);

    let diff = &a - &b;
    let coeffs = diff.clone_to_coefficient();

    for i in 0..8 {
        let expected = (i * 2) as u64;
        assert_eq!(coeffs.coefficients()[i].to_u1024().0[0], expected);
    }
}

#[test]
fn test_negation() {
    let ctx = make_ctx();
    let a = RingElement::new(vec![fp!(5u64); 8], ctx.clone());

    let neg_a = -&a;
    let sum = &a + &neg_a;

    assert!(sum.is_zero());
}

#[test]
fn test_multiplication_produces_ntt_state() {
    let ctx = make_ctx();
    let a = RingElement::new(vec![fp!(1u64); 8], ctx.clone());
    let b = RingElement::new(vec![fp!(2u64); 8], ctx);

    let product = &a * &b;
    assert_eq!(product.state(), RingElementState::Ntt);
}

#[test]
fn test_multiplication_with_one() {
    let ctx = make_ctx();
    let a = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx.clone());
    let one = RingElement::one(ctx);

    let product = &a * &one;
    let result = product.clone_to_coefficient();

    // a * 1 should equal a
    assert_eq!(a, result);
}

#[test]
fn test_multiplication_with_zero() {
    let ctx = make_ctx();
    let a = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx.clone());
    let zero = RingElement::zero(ctx);

    let product = &a * &zero;
    let result = product.clone_to_coefficient();

    assert!(result.is_zero());
}

#[test]
fn test_scale() {
    let ctx = make_ctx();
    let a = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx);
    let scalar = fp!(3u64);

    let scaled = a.scale(&scalar);
    let coeffs = scaled.coefficients();

    for i in 0..8 {
        let expected = (i * 3) as u64;
        assert_eq!(coeffs[i].to_u1024().0[0], expected);
    }
}

#[test]
fn test_equality_different_states() {
    let ctx = make_ctx();
    let a = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx.clone());

    // Create same element in NTT form
    let b = a.clone_to_ntt();

    // Should be equal despite different states
    assert_eq!(a, b);
}

#[test]
fn test_from_ntt() {
    let ctx = make_ctx();
    let coeffs: Vec<FieldElement<DefaultFieldConfig>> = (0..8).map(|i| fp!(i as u64)).collect();

    let elem = RingElement::new(coeffs.clone(), ctx.clone());
    let ntt_elem = elem.clone_to_ntt();

    // Create new element from NTT values
    let from_ntt = RingElement::from_ntt(ntt_elem.data().to_vec(), ctx);
    assert_eq!(from_ntt.state(), RingElementState::Ntt);

    // Should equal original when converted
    assert_eq!(elem, from_ntt);
}

#[test]
fn test_mixed_state_addition() {
    let ctx = make_ctx();
    let a = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx.clone());
    let b = RingElement::new((0..8).map(|i| fp!((i + 1) as u64)).collect(), ctx);

    // Convert a to NTT
    let a_ntt = a.clone_to_ntt();

    // Add NTT + coefficient
    let sum = &a_ntt + &b;

    // Verify result
    let direct_sum = &a + &b;
    assert_eq!(sum, direct_sum);
}

#[test]
fn test_commutativity_of_addition() {
    let ctx = make_ctx();
    let a = RingElement::new((0..8).map(|i| fp!(i as u64)).collect(), ctx.clone());
    let b = RingElement::new((0..8).map(|i| fp!((i * 2 + 3) as u64)).collect(), ctx);

    let ab = &a + &b;
    let ba = &b + &a;

    assert_eq!(ab, ba);
}

#[test]
fn test_commutativity_of_multiplication() {
    let ctx = make_ctx();
    let a = RingElement::new((0..8).map(|i| fp!((i + 1) as u64)).collect(), ctx.clone());
    let b = RingElement::new((0..8).map(|i| fp!((i + 2) as u64)).collect(), ctx);

    let ab = &a * &b;
    let ba = &b * &a;

    assert_eq!(ab, ba);
}

#[test]
fn test_distributivity() {
    let ctx = make_ctx();
    let a = RingElement::new(
        vec![
            fp!(1u64),
            fp!(2u64),
            fp!(0u64),
            fp!(0u64),
            fp!(0u64),
            fp!(0u64),
            fp!(0u64),
            fp!(0u64),
        ],
        ctx.clone(),
    );
    let b = RingElement::new(
        vec![
            fp!(3u64),
            fp!(0u64),
            fp!(0u64),
            fp!(0u64),
            fp!(0u64),
            fp!(0u64),
            fp!(0u64),
            fp!(0u64),
        ],
        ctx.clone(),
    );
    let c = RingElement::new(
        vec![
            fp!(4u64),
            fp!(0u64),
            fp!(0u64),
            fp!(0u64),
            fp!(0u64),
            fp!(0u64),
            fp!(0u64),
            fp!(0u64),
        ],
        ctx,
    );

    // a * (b + c) should equal a*b + a*c
    let b_plus_c = &b + &c;
    let lhs = &a * &b_plus_c;

    let ab = &a * &b;
    let ac = &a * &c;
    let rhs = &ab + &ac;

    assert_eq!(lhs, rhs);
}

#[test]
#[should_panic(expected = "Coefficient length must match NTT context degree")]
fn test_wrong_coefficient_length_panics() {
    let ctx = make_ctx();
    let _elem = RingElement::new(vec![fp!(1u64); 4], ctx); // Wrong size
}

#[test]
#[should_panic(expected = "Ring elements must share the same NTT context")]
fn test_different_contexts_panics() {
    let ctx1 = make_ctx();
    let ctx2 = make_ctx(); // Different Arc instance

    let a = RingElement::new(vec![fp!(1u64); 8], ctx1);
    let b = RingElement::new(vec![fp!(1u64); 8], ctx2);

    let _ = &a + &b; // Should panic
}
