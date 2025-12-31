use lumen_math::{DefaultFieldConfig, FieldElement, U1024, u1024};

// Verify const construction works at compile time
const VAL: FieldElement<DefaultFieldConfig> =
    FieldElement::new(U1024([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]));

// Verify const identity works at compile time
const ZERO: FieldElement<DefaultFieldConfig> = FieldElement::zero();
const ONE: FieldElement<DefaultFieldConfig> = FieldElement::one();

// Verify const raw construction
const RAW: FieldElement<DefaultFieldConfig> =
    FieldElement::from_montgomery(U1024([5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]));

#[test]
fn test_const_vals() {
    // These assertions run at runtime, but the values were created at compile time.
    assert_eq!(VAL.to_u1024(), u1024!(1));
    assert!(ZERO.is_zero());
    assert_eq!(ONE.to_u1024(), u1024!(1));
    assert_eq!(RAW.value, u1024!(5));
}
