use mathlib::{BigInt, U1024};
use num_bigint::BigUint;
use num_traits::One;
use proptest::prelude::*;

fn u1024_to_biguint(u: &U1024) -> BigUint {
    let mut bytes = Vec::new();
    for limb in u.0.iter() {
        bytes.extend_from_slice(&limb.to_le_bytes());
    }
    BigUint::from_bytes_le(&bytes)
}

prop_compose! {
    fn arb_u1024()(limbs in prop::array::uniform16(any::<u64>())) -> U1024 {
        U1024(limbs)
    }
}

proptest! {
    #[test]
    fn test_add_properties(a in arb_u1024(), b in arb_u1024()) {
        let (res_our, carry_our) = a.carrying_add(&b);
        let res_our_big = u1024_to_biguint(&res_our);

        let a_big = u1024_to_biguint(&a);
        let b_big = u1024_to_biguint(&b);
        let res_oracle = a_big.clone() + b_big.clone();


        let modulus = BigUint::one() << 1024;
        let expected_low = &res_oracle % &modulus;

        prop_assert_eq!(&res_our_big, &expected_low, "Addition result mismatch");

        let expected_carry = &res_oracle >= &modulus;
        prop_assert_eq!(carry_our, expected_carry, "Carry flag mismatch");
    }

    #[test]
    fn test_mul_properties(a in arb_u1024(), b in arb_u1024()) {
        let (low, high) = a.full_mul(&b);

        let low_big = u1024_to_biguint(&low);
        let high_big = u1024_to_biguint(&high);
        let combined = low_big + (high_big << 1024);

        let a_big = u1024_to_biguint(&a);
        let b_big = u1024_to_biguint(&b);
        let res_oracle = a_big * b_big;

        prop_assert_eq!(combined, res_oracle, "Multiplication result mismatch");
    }
}
