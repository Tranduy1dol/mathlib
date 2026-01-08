use lumen_math::{DefaultFieldConfig, FieldConfig, FieldElement, fp, u1024};

#[test]
fn test_field_element_arithmetic() {
    let a = fp!(5u64);
    let b = fp!(3u64);

    // Test addition
    let sum = a + b;
    assert!(!sum.is_zero());

    // Test subtraction
    let diff = a - b;
    assert_eq!((diff + b).to_u1024(), a.to_u1024());

    // Test multiplication
    let prod = a * b;
    assert_eq!((prod * a.inv()).to_u1024(), b.to_u1024());

    // Test negation
    let neg_a = -a;
    assert_eq!((a + neg_a).to_u1024(), u1024!(0));
}

#[test]
fn test_field_element_zero_and_one() {
    let zero = FieldElement::<DefaultFieldConfig>::zero();
    let one = FieldElement::<DefaultFieldConfig>::one();

    assert!(zero.is_zero());
    assert!(!one.is_zero());

    // Zero properties
    assert_eq!((zero + zero).to_u1024(), u1024!(0));
    assert_eq!((zero * one).to_u1024(), u1024!(0));
    assert_eq!((one * one).to_u1024(), u1024!(1));

    // Additive identity
    let a = fp!(42u64);
    assert_eq!((a + zero).to_u1024(), a.to_u1024());

    // Multiplicative identity
    assert_eq!((a * one).to_u1024(), a.to_u1024());
}

#[test]
fn test_field_element_inverse() {
    let a = fp!(7u64);
    let a_inv = a.inv();

    // a * a^-1 = 1
    assert_eq!((a * a_inv).to_u1024(), u1024!(1));

    // Test inverse of 1
    let one = FieldElement::<DefaultFieldConfig>::one();
    assert_eq!(one.inv().to_u1024(), u1024!(1));
}

#[test]
fn test_field_element_double_and_square() {
    let a = fp!(5u64);

    // Test double
    let doubled = a.double();
    assert_eq!(doubled.to_u1024(), (a + a).to_u1024());

    // Test square
    let squared = a.square();
    assert_eq!(squared.to_u1024(), (a * a).to_u1024());
}

#[test]
fn test_field_element_from_montgomery() {
    let raw = u1024!(42);
    let elem = FieldElement::<DefaultFieldConfig>::from_montgomery(raw);

    // from_montgomery should create an element with the raw value
    assert_eq!(elem.value, raw);
}

#[test]
fn test_field_config_to_montgomery_context() {
    let ctx = DefaultFieldConfig::to_montgomery_context();

    // Verify the context has the correct values
    assert_eq!(ctx.modulus, DefaultFieldConfig::MODULUS);
    assert_eq!(ctx.r2, DefaultFieldConfig::R2);
    assert_eq!(ctx.n_prime, DefaultFieldConfig::N_PRIME);
    assert_eq!(ctx.root_of_unity, DefaultFieldConfig::ROOT_OF_UNITY);
}

#[test]
fn test_fp_macro_variations() {
    // Test with u64
    let a = fp!(42u64);
    assert_eq!(a.to_u1024(), u1024!(42));

    // Test with default config (implicit)
    let b = fp!(5u64);
    assert_eq!(b.to_u1024(), u1024!(5));
}

#[test]
fn test_field_element_negation_properties() {
    let a = fp!(123u64);
    let b = fp!(456u64);

    // -(-a) = a
    let neg_neg_a = -(-a);
    assert_eq!(neg_neg_a.to_u1024(), a.to_u1024());

    // -(a + b) = -a + -b
    let neg_sum = -(a + b);
    let sum_neg = (-a) + (-b);
    assert_eq!(neg_sum.to_u1024(), sum_neg.to_u1024());
}

#[test]
fn test_field_element_distributive_property() {
    let a = fp!(3u64);
    let b = fp!(5u64);
    let c = fp!(7u64);

    // a * (b + c) = a*b + a*c
    let left = a * (b + c);
    let right = (a * b) + (a * c);
    assert_eq!(left.to_u1024(), right.to_u1024());
}

#[test]
fn test_field_element_commutative_property() {
    let a = fp!(11u64);
    let b = fp!(13u64);

    // Addition is commutative: a + b = b + a
    assert_eq!((a + b).to_u1024(), (b + a).to_u1024());

    // Multiplication is commutative: a * b = b * a
    assert_eq!((a * b).to_u1024(), (b * a).to_u1024());
}

#[test]
fn test_field_element_associative_property() {
    let a = fp!(2u64);
    let b = fp!(3u64);
    let c = fp!(5u64);

    // Addition is associative: (a + b) + c = a + (b + c)
    let left_add = (a + b) + c;
    let right_add = a + (b + c);
    assert_eq!(left_add.to_u1024(), right_add.to_u1024());

    // Multiplication is associative: (a * b) * c = a * (b * c)
    let left_mul = (a * b) * c;
    let right_mul = a * (b * c);
    assert_eq!(left_mul.to_u1024(), right_mul.to_u1024());
}

#[test]
fn test_field_element_clone_copy() {
    let a = fp!(42u64);

    // Test Clone
    let b = a;
    assert_eq!(a.to_u1024(), b.to_u1024());

    // Test Copy (implicit)
    let c = a;
    assert_eq!(a.to_u1024(), c.to_u1024());
}

#[test]
fn test_field_element_debug_format() {
    let a = fp!(42u64);
    let debug_str = format!("{:?}", a);

    // Should contain the value
    assert!(!debug_str.is_empty());
}

#[test]
fn test_const_field_element_construction() {
    // These constants are created at compile time
    const ZERO: FieldElement<DefaultFieldConfig> = FieldElement::zero();
    const ONE: FieldElement<DefaultFieldConfig> = FieldElement::one();

    assert!(ZERO.is_zero());
    assert_eq!(ONE.to_u1024(), u1024!(1));
}
