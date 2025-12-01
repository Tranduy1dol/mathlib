use crate::big_int::u1024::{LIMBS, U1024};
use crate::traits::BigInt;

#[inline(always)]
pub fn add(a: &U1024, b: &U1024) -> (U1024, bool) {
    let mut ret = U1024::zero();
    let mut carry = 0u64;

    for i in 0..LIMBS {
        let (sum1, c1) = a.0[i].overflowing_add(b.0[i]);
        let (sum2, c2) = sum1.overflowing_add(carry);
        ret.0[i] = sum2;
        carry = (c1 as u64) + (c2 as u64);
    }
    (ret, carry != 0)
}

#[inline(always)]
pub fn sub(a: &U1024, b: &U1024) -> (U1024, bool) {
    let mut ret = U1024::zero();
    let mut borrow = 0u64;

    for i in 0..LIMBS {
        let (diff1, b1) = a.0[i].overflowing_sub(b.0[i]);
        let (diff2, b2) = diff1.overflowing_sub(borrow);
        ret.0[i] = diff2;
        borrow = (b1 as u64) + (b2 as u64);
    }
    (ret, borrow != 0)
}

pub fn mul(a: &U1024, b: &U1024) -> (U1024, U1024) {
    let mut res = [0u64; LIMBS * 2];

    for i in 0..LIMBS {
        let mut carry = 0u64;
        for j in 0..LIMBS {
            let k = i + j;
            let val = res[k] as u128 + (a.0[i] as u128 * b.0[j] as u128) + carry as u128;
            res[k] = val as u64;
            carry = (val >> 64) as u64;
        }
        let mut k = i + LIMBS;
        while carry > 0 && k < LIMBS * 2 {
            let val = res[k] as u128 + carry as u128;
            res[k] = val as u64;
            carry = (val >> 64) as u64;
            k += 1;
        }
    }

    let mut low = U1024::zero();
    let mut high = U1024::zero();
    low.0.copy_from_slice(&res[0..LIMBS]);
    high.0.copy_from_slice(&res[LIMBS..LIMBS * 2]);
    (low, high)
}
