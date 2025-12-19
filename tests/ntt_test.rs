use mathlib::{DefaultFieldConfig, FieldElement, fp, poly::ntt, u1024};

#[test]
fn test_ntt_basic() {
    let size = 4;

    // Use default config implicitly via fp! or explicitly via generic
    let mut coeffs = vec![FieldElement::<DefaultFieldConfig>::one(); size];

    println!("Input: {:?}", coeffs);

    ntt(&mut coeffs);

    println!("Output (Point Values): {:?}", coeffs);

    let expected_0 = fp!(u1024!(4)); // Uses DefaultFieldConfig
    let expected_other = FieldElement::<DefaultFieldConfig>::zero();

    assert_eq!(coeffs[0], expected_0);
    assert_eq!(coeffs[1], expected_other);
    assert_eq!(coeffs[2], expected_other);
    assert_eq!(coeffs[3], expected_other);
}
