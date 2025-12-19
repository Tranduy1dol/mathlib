use mathlib::{DefaultFieldConfig, FieldElement, bit_reverse, fp, intt, ntt};

#[test]
fn test_ntt_basic_sizes() {
    let sizes = vec![2, 4, 8, 16, 32];

    for size in sizes {
        let mut coeffs: Vec<_> = (0..size)
            .map(|i| {
                FieldElement::<DefaultFieldConfig>::from_montgomery(mathlib::U1024::from_u64(
                    i as u64,
                ))
            })
            .collect();

        let original = coeffs.clone();

        // Apply NTT then INTT
        ntt(&mut coeffs);
        intt(&mut coeffs);

        // Should get back original values
        for (a, b) in original.iter().zip(coeffs.iter()) {
            assert_eq!(a.value, b.value);
        }
    }
}

#[test]
fn test_ntt_zero_polynomial() {
    let size = 8;
    let mut coeffs = vec![FieldElement::<DefaultFieldConfig>::zero(); size];

    ntt(&mut coeffs);

    // NTT of all zeros should be all zeros
    for c in coeffs.iter() {
        assert!(c.is_zero());
    }
}

#[test]
fn test_ntt_one_polynomial() {
    let _size = 4;
    let one = FieldElement::<DefaultFieldConfig>::one();
    let zero = FieldElement::<DefaultFieldConfig>::zero();

    let mut coeffs = vec![one, zero, zero, zero];
    let first_value = coeffs[0].value;

    ntt(&mut coeffs);

    // NTT of [1, 0, 0, 0] should be [1, 1, 1, 1]
    for c in coeffs.iter() {
        assert_eq!(c.value, first_value);
    }
}

#[test]
fn test_intt_after_ntt() {
    let size = 16;
    let mut coeffs: Vec<_> = (0..size).map(|i| fp!(i as u64)).collect();
    let original = coeffs.clone();

    ntt(&mut coeffs);
    intt(&mut coeffs);

    // Round-trip should preserve values
    for (orig, result) in original.iter().zip(coeffs.iter()) {
        assert_eq!(orig.to_u1024(), result.to_u1024());
    }
}

#[test]
fn test_bit_reverse_basic() {
    let mut coeffs = vec![fp!(0u64), fp!(1u64), fp!(2u64), fp!(3u64)];

    bit_reverse(&mut coeffs);

    // For size 4, bit reverse of [0,1,2,3] should be [0,2,1,3]
    assert_eq!(coeffs[0].to_u1024(), fp!(0u64).to_u1024());
    assert_eq!(coeffs[1].to_u1024(), fp!(2u64).to_u1024());
    assert_eq!(coeffs[2].to_u1024(), fp!(1u64).to_u1024());
    assert_eq!(coeffs[3].to_u1024(), fp!(3u64).to_u1024());
}

#[test]
fn test_bit_reverse_twice_identity() {
    let mut coeffs = vec![fp!(1u64), fp!(2u64), fp!(3u64), fp!(4u64)];
    let original = coeffs.clone();

    bit_reverse(&mut coeffs);
    bit_reverse(&mut coeffs);

    // Applying bit_reverse twice should give back original
    for (a, b) in original.iter().zip(coeffs.iter()) {
        assert_eq!(a.to_u1024(), b.to_u1024());
    }
}

#[test]
fn test_ntt_size_2() {
    let mut coeffs = vec![fp!(5u64), fp!(3u64)];
    let original = coeffs.clone();

    ntt(&mut coeffs);
    intt(&mut coeffs);

    for (a, b) in original.iter().zip(coeffs.iter()) {
        assert_eq!(a.to_u1024(), b.to_u1024());
    }
}

#[test]
fn test_ntt_linearity() {
    let size = 8;
    let a_coeffs: Vec<_> = (0..size).map(|i| fp!(i as u64)).collect();
    let b_coeffs: Vec<_> = (0..size).map(|i| fp!((i + 1) as u64)).collect();

    // NTT(a + b) = NTT(a) + NTT(b)
    let mut sum_coeffs: Vec<_> = a_coeffs
        .iter()
        .zip(b_coeffs.iter())
        .map(|(a, b)| *a + *b)
        .collect();

    let mut a_copy = a_coeffs.clone();
    let mut b_copy = b_coeffs.clone();

    ntt(&mut sum_coeffs);
    ntt(&mut a_copy);
    ntt(&mut b_copy);

    for i in 0..size {
        let expected = a_copy[i] + b_copy[i];
        assert_eq!(sum_coeffs[i].to_u1024(), expected.to_u1024());
    }
}

#[test]
#[should_panic(expected = "NTT size must be power of two")]
fn test_ntt_non_power_of_two() {
    let mut coeffs = vec![fp!(1u64), fp!(2u64), fp!(3u64)]; // Size 3 is not power of 2
    ntt(&mut coeffs);
}

#[test]
fn test_ntt_large_size() {
    let size = 256;
    let mut coeffs: Vec<_> = (0..size).map(|i| fp!((i % 100) as u64)).collect();
    let original = coeffs.clone();

    ntt(&mut coeffs);
    intt(&mut coeffs);

    for (a, b) in original.iter().zip(coeffs.iter()) {
        assert_eq!(a.to_u1024(), b.to_u1024());
    }
}
