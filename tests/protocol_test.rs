use lumen_math::protocol::{
    CrtError, chinese_remainder, chinese_remainder_solver, extended_gcd, mod_inverse,
};
use lumen_math::{U1024, i1024};

#[test]
fn test_extended_gcd_integration() {
    // gcd(240, 46)
    // 240 = 46*5 + 10
    // 46 = 10*4 + 6
    // 10 = 6*1 + 4
    // 6 = 4*1 + 2
    // 4 = 2*2 + 0
    // gcd is 2.
    // 2 = 6 - 4
    //   = 6 - (10 - 6) = 2*6 - 10
    //   = 2*(46 - 4*10) - 10 = 2*46 - 9*10
    //   = 2*46 - 9*(240 - 5*46) = 2*46 - 9*240 + 45*46
    //   = 47*46 - 9*240
    // Check: 47*46 = 2162, 9*240 = 2160. Diff is 2. Correct.

    let a = U1024::from_u64(240);
    let b = U1024::from_u64(46);
    let res = extended_gcd(a, b);

    assert_eq!(res.gcd, U1024::from_u64(2));

    // Check linear combination: ax + by = gcd
    // x = -9, y = 47
    assert_eq!(res.x, i1024!(-9));
    assert_eq!(res.y, i1024!(47u64));

    let ax = i1024!(a) * res.x;
    let by = i1024!(b) * res.y;
    assert_eq!((ax + by).magnitude(), res.gcd);
}

#[test]
fn test_mod_inverse_integration() {
    // 17 * x = 1 mod 43
    // 17 * 38 = 646. 646 / 43 = 15 rem 1.
    // x = 38
    let val = U1024::from_u64(17);
    let modulus = U1024::from_u64(43);

    let inv = mod_inverse(val, modulus).expect("Inverse should exist");
    assert_eq!(inv, U1024::from_u64(38));

    // Check cyclic property
    let val_back = mod_inverse(inv, modulus).unwrap();
    assert_eq!(val_back, val);
}

#[test]
fn test_crt_integration() {
    // Example from Wikipedia
    // x = 0 mod 3
    // x = 3 mod 4
    // x = 4 mod 5
    // x = 39

    let remainders = vec![U1024::from_u64(0), U1024::from_u64(3), U1024::from_u64(4)];
    let moduli = vec![U1024::from_u64(3), U1024::from_u64(4), U1024::from_u64(5)];

    let res = chinese_remainder_solver(&remainders, &moduli).unwrap();
    assert_eq!(res, U1024::from_u64(39));

    // Error cases
    let bad_res = chinese_remainder_solver(
        &[U1024::from_u64(1)],
        &[U1024::from_u64(2), U1024::from_u64(3)],
    );
    assert_eq!(bad_res, Err(CrtError::LengthMismatch));

    let not_coprime = chinese_remainder_solver(
        &[U1024::from_u64(1), U1024::from_u64(1)],
        &[U1024::from_u64(2), U1024::from_u64(4)],
    );
    assert_eq!(not_coprime, Err(CrtError::ModuliNotCoprime));

    // Check overflow
    // U1024::MAX is huge. Two of them multiplied overflows.
    let max_val = U1024([u64::MAX; 16]);
    let overflow = chinese_remainder_solver(
        &[U1024::from_u64(1), U1024::from_u64(1)],
        &[max_val, max_val],
    );
    assert_eq!(overflow, Err(CrtError::ProductOverflow));
}

#[test]
fn test_simple_crt_helper() {
    // x = 1 mod 2, x = 2 mod 3 => x = 5 (mod 6)
    let res = chinese_remainder(
        U1024::from_u64(1),
        U1024::from_u64(2),
        U1024::from_u64(2),
        U1024::from_u64(3),
    )
    .unwrap();
    assert_eq!(res, U1024::from_u64(5));
}
