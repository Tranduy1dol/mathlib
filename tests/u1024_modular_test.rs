use lumen_math::{U1024, u1024};

#[test]
fn test_u1024_mod_mul_basic() {
    let a = u1024!(10u64);
    let b = u1024!(20u64);
    let m = u1024!(23u64);

    // 10 * 20 = 200
    // 200 = 8 * 23 + 16
    let res = a.mod_mul(&b, &m);
    assert_eq!(res, u1024!(16u64));
}

#[test]
fn test_u1024_mod_mul_large() {
    // Operations with large numbers
    let m = u1024!(1_000_000_000_000_000_007u64); // large u64 prime
    let a = m - u1024!(1u64); // m-1
    let b = u1024!(2u64);

    // (m-1) * 2 = 2m - 2 = -2 = m-2 (mod m)
    let res = a.mod_mul(&b, &m);
    assert_eq!(res, m - u1024!(2u64));
}

#[test]
fn test_u1024_mod_pow_basic() {
    let base = u1024!(2u64);
    let exp = u1024!(10u64);
    let m = u1024!(1000u64);

    // 2^10 = 1024
    // 1024 mod 1000 = 24
    let res = base.mod_pow(&exp, &m);
    assert_eq!(res, u1024!(24u64));
}

#[test]
fn test_u1024_mod_pow_zero_exp() {
    let base = u1024!(12345u64);
    let exp = u1024!(0u64);
    let m = u1024!(100u64);

    // x^0 = 1
    let res = base.mod_pow(&exp, &m);
    assert_eq!(res, u1024!(1u64));
}

#[test]
fn test_u1024_mod_pow_one_modulus() {
    let base = u1024!(123u64);
    let exp = u1024!(456u64);
    let m = u1024!(1u64);

    // x mod 1 is always 0
    let res = base.mod_pow(&exp, &m);
    assert_eq!(res, U1024::ZERO);
}

#[test]
fn test_u1024_cge_alias() {
    let base = u1024!(5u64);
    let exp = u1024!(3u64);
    let m = u1024!(13u64);

    // 5^3 = 125
    // 125 = 9 * 13 + 8
    assert_eq!(base.cge(&exp, &m), u1024!(8u64));
    assert_eq!(base.cge(&exp, &m), base.mod_pow(&exp, &m));
}
