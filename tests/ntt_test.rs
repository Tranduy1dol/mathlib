use mathlib::{FieldElement, fp, get_params, poly::ntt, u1024};

#[test]
fn test_ntt_basic() {
    let params = get_params();
    let size = 4;

    let mut coeffs = vec![FieldElement::one(params); size];

    println!("Input: {:?}", coeffs);

    ntt(&mut coeffs);

    println!("Output (Point Values): {:?}", coeffs);

    let expected_0 = fp!(u1024!(4), params);
    let expected_other = FieldElement::zero(params);

    assert_eq!(coeffs[0], expected_0);
    assert_eq!(coeffs[1], expected_other);
    assert_eq!(coeffs[2], expected_other);
    assert_eq!(coeffs[3], expected_other);
}
