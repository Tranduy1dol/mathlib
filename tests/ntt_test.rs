use mathlib::U1024;
use mathlib::field::constants::get_params;
use mathlib::field::element::FieldElement;
use mathlib::poly::ntt::ntt;
use mathlib::traits::BigInt;

#[test]
fn test_ntt_basic() {
    let params = get_params();
    let size = 4;

    let mut coeffs = vec![FieldElement::one(params); size];

    println!("Input: {:?}", coeffs);

    ntt(&mut coeffs);

    println!("Output (Point Values): {:?}", coeffs);

    let expected_0 = FieldElement::new(U1024::from_u64(4), params);
    let expected_other = FieldElement::zero(params);

    assert_eq!(coeffs[0], expected_0);
    assert_eq!(coeffs[1], expected_other);
    assert_eq!(coeffs[2], expected_other);
    assert_eq!(coeffs[3], expected_other);
}
