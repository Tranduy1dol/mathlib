use std::ops::{Add, BitXor, Mul, Sub};

use crate::num::{u128::U128, u512::U512};

#[repr(align(32))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct U256(pub [u64; 4]);

impl U256 {
    pub const ZERO: Self = Self([0; 4]);
    pub const MAX: Self = Self([u64::MAX; 4]);

    pub fn mul_karatsuba(&self, rhs: &Self) -> U512 {
        let a_low = U128([self.0[0], self.0[1]]);
        let a_high = U128([self.0[2], self.0[3]]);
        let b_low = U128([rhs.0[0], rhs.0[1]]);
        let b_high = U128([rhs.0[2], rhs.0[3]]);

        let z0 = a_low.full_mul(&b_low);
        let z2 = a_high.full_mul(&b_high);

        let (a_sum, a_carry) = a_low.carrying_add(&a_high);
        let (b_sum, b_carry) = b_low.carrying_add(&b_high);

        let z1_combined = a_sum.full_mul(&b_sum);

        let mut result = U512([0; 8]);
        result.0[0..4].copy_from_slice(&z0.0);
        result.0[4..8].copy_from_slice(&z2.0);

        let (mid, borrow1) = z1_combined.borrowing_sub(&z0);
        let (mid, borrow2) = mid.borrowing_sub(&z2);
        let borrow_val = (borrow1 as u64) + (borrow2 as u64);

        let mut carry = 0u64;
        for i in 0..4 {
            let (r, c1) = result.0[i + 2].overflowing_add(mid.0[i]);
            let (r, c2) = r.overflowing_add(carry);
            result.0[i + 2] = r;
            carry = (c1 as u64) + (c2 as u64);
        }
        let mut i = 6;
        while carry > 0 && i < 8 {
            let (r, c) = result.0[i].overflowing_add(carry);
            result.0[i] = r;
            carry = c as u64;
            i += 1;
        }

        let mut borrow = borrow_val;
        i = 6;
        while borrow > 0 && i < 8 {
            let (r, b) = result.0[i].overflowing_sub(borrow);
            result.0[i] = r;
            borrow = b as u64;
            i += 1;
        }

        if a_carry {
            carry = 0;
            for i in 0..2 {
                let (r, c1) = result.0[i + 4].overflowing_add(b_sum.0[i]);
                let (r, c2) = r.overflowing_add(carry);
                result.0[i + 4] = r;
                carry = (c1 as u64) + (c2 as u64);
            }
            i = 6;
            while carry > 0 && i < 8 {
                let (r, c) = result.0[i].overflowing_add(carry);
                result.0[i] = r;
                carry = c as u64;
                i += 1;
            }
        }
        if b_carry {
            carry = 0;
            for i in 0..2 {
                let (r, c1) = result.0[i + 4].overflowing_add(a_sum.0[i]);
                let (r, c2) = r.overflowing_add(carry);
                result.0[i + 4] = r;
                carry = (c1 as u64) + (c2 as u64);
            }
            i = 6;
            while carry > 0 && i < 8 {
                let (r, c) = result.0[i].overflowing_add(carry);
                result.0[i] = r;
                carry = c as u64;
                i += 1;
            }
        }

        if a_carry && b_carry {
            carry = 1;
            i = 6;
            while carry > 0 && i < 8 {
                let (r, c) = result.0[i].overflowing_add(carry);
                result.0[i] = r;
                carry = c as u64;
                i += 1;
            }
        }

        result
    }

    pub fn full_mul(&self, rhs: &Self) -> U512 {
        let mut result = U512::ZERO;

        for i in 0..4 {
            let mut carry: u128 = 0;
            for j in 0..4 {
                let a_limb = self.0[i] as u128;
                let b_limb = rhs.0[j] as u128;

                let result_limb = result.0[i + j] as u128;

                let product = a_limb * b_limb + result_limb + carry;

                result.0[i + j] = product as u64;
                carry = product >> 64;
            }

            result.0[i + 4] += carry as u64;
        }

        result
    }

    pub fn xor_safe(&self, rhs: &Self) -> Self {
        let mut result = U256([0; 4]);
        for i in 0..4 {
            result.0[i] = self.0[i] ^ rhs.0[i];
        }
        result
    }

    pub fn carrying_add(&self, rhs: &Self) -> (Self, bool) {
        let mut result = U256([0; 4]);
        let mut carry = 0;

        for i in 0..4 {
            let (sum1, carry1) = self.0[i].overflowing_add(rhs.0[i]);
            let (sum2, carry2) = sum1.overflowing_add(carry);

            result.0[i] = sum2;
            carry = (carry1 as u64) + (carry2 as u64);
        }

        (result, carry != 0)
    }

    pub fn wrapping_add(&self, rhs: &Self) -> Self {
        self.carrying_add(rhs).0
    }

    pub fn borrowing_sub(&self, rhs: &Self) -> (Self, bool) {
        let mut result = U256([0; 4]);
        let mut borrow: u64 = 0;

        for i in 0..4 {
            let (diff1, borrow1) = self.0[i].overflowing_sub(rhs.0[i]);
            let (diff2, borrow2) = diff1.overflowing_sub(borrow);

            result.0[i] = diff2;
            borrow = (borrow1 as u64) + (borrow2 as u64);
        }

        (result, borrow != 0)
    }

    pub fn wrapping_sub(&self, rhs: &Self) -> Self {
        self.borrowing_sub(rhs).0
    }
}

impl Add for U256 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        self.wrapping_add(&rhs)
    }
}

impl<'b> Add<&'b U256> for &U256 {
    type Output = U256;

    fn add(self, rhs: &'b U256) -> Self::Output {
        self.wrapping_add(rhs)
    }
}

impl Sub for U256 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.wrapping_sub(&rhs)
    }
}

impl<'b> Sub<&'b U256> for &U256 {
    type Output = U256;

    fn sub(self, rhs: &'b U256) -> Self::Output {
        self.wrapping_sub(rhs)
    }
}

impl BitXor for U256 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        if is_x86_feature_detected!("avx2") {
            unsafe { crate::arch::x86_64::avx2::xor_avx2(&self, &rhs) }
        } else {
            self.xor_safe(&rhs)
        }
    }
}

impl<'b> BitXor<&'b U256> for &U256 {
    type Output = U256;

    fn bitxor(self, rhs: &'b U256) -> Self::Output {
        if is_x86_feature_detected!("avx2") {
            unsafe { crate::arch::x86_64::avx2::xor_avx2(self, rhs) }
        } else {
            self.xor_safe(rhs)
        }
    }
}

impl Mul for U256 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let full_result = self.full_mul(&rhs);
        U256([
            full_result.0[0],
            full_result.0[1],
            full_result.0[2],
            full_result.0[3],
        ])
    }
}

impl<'b> Mul<&'b U256> for &U256 {
    type Output = U256;

    fn mul(self, rhs: &'b U256) -> Self::Output {
        let full_result = self.full_mul(rhs);
        U256([
            full_result.0[0],
            full_result.0[1],
            full_result.0[2],
            full_result.0[3],
        ])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_carrying_add() {
        let a = U256([1, 0, 0, 0]);
        let b = U256([2, 0, 0, 0]);
        let (res, carry) = a.carrying_add(&b);
        assert_eq!(res, U256([3, 0, 0, 0]));
        assert!(!carry);

        let a = U256([u64::MAX, 0, 0, 0]);
        let b = U256([1, 0, 0, 0]);
        let (res, carry) = a.carrying_add(&b);
        assert_eq!(res, U256([0, 1, 0, 0]));
        assert!(!carry);

        let a = U256::MAX;
        let b = U256([1, 0, 0, 0]);
        let (res, carry) = a.carrying_add(&b);
        assert_eq!(res, U256([0, 0, 0, 0]));
        assert!(carry);
    }

    #[test]
    fn test_borrowing_sub() {
        let a = U256([3, 0, 0, 0]);
        let b = U256([2, 0, 0, 0]);
        let (res, borrow) = a.borrowing_sub(&b);
        assert_eq!(res, U256([1, 0, 0, 0]));
        assert!(!borrow);

        let a = U256([0, 1, 0, 0]);
        let b = U256([1, 0, 0, 0]);
        let (res, borrow) = a.borrowing_sub(&b);
        assert_eq!(res, U256([u64::MAX, 0, 0, 0]));
        assert!(!borrow);

        let a = U256::ZERO;
        let b = U256([1, 0, 0, 0]);
        let (res, borrow) = a.borrowing_sub(&b);
        assert_eq!(res, U256([u64::MAX, u64::MAX, u64::MAX, u64::MAX]));
        assert!(borrow);
    }

    #[test]
    fn test_full_mul() {
        let a = U256::ZERO;
        let b = U256::MAX;
        assert_eq!(a.full_mul(&b), U512::ZERO);

        let a = U256([1, 0, 0, 0]);
        let b = U256([2, 0, 0, 0]);
        assert_eq!(a.full_mul(&b), U512([2, 0, 0, 0, 0, 0, 0, 0]));

        let a = U256([u64::MAX, 0, 0, 0]);
        let b = U256([2, 0, 0, 0]);
        let expected = U512([18446744073709551614, 1, 0, 0, 0, 0, 0, 0]);
        assert_eq!(a.full_mul(&b), expected);
    }

    #[test]
    fn test_mul_karatsuba() {
        let a = U256::ZERO;
        let b = U256::MAX;
        assert_eq!(a.mul_karatsuba(&b), a.full_mul(&b));

        let a = U256([1, 0, 0, 0]);
        let b = U256([2, 0, 0, 0]);
        assert_eq!(a.mul_karatsuba(&b), a.full_mul(&b));

        let a = U256([u64::MAX, 0, 0, 0]);
        let b = U256([2, 0, 0, 0]);
        assert_eq!(a.mul_karatsuba(&b), a.full_mul(&b));

        let a = U256([1, 2, 3, 4]);
        let b = U256([5, 6, 7, 8]);
        assert_eq!(a.mul_karatsuba(&b), a.full_mul(&b));

        let a = U256::MAX;
        let b = U256::MAX;
        assert_eq!(a.mul_karatsuba(&b), a.full_mul(&b));
    }

    #[test]
    fn test_wrapping_add() {
        let a = U256([1, 0, 0, 0]);
        let b = U256([2, 0, 0, 0]);
        assert_eq!(a.wrapping_add(&b), U256([3, 0, 0, 0]));

        let a = U256::MAX;
        let b = U256([1, 0, 0, 0]);
        assert_eq!(a.wrapping_add(&b), U256::ZERO);
    }

    #[test]
    fn test_wrapping_sub() {
        let a = U256([3, 0, 0, 0]);
        let b = U256([2, 0, 0, 0]);
        assert_eq!(a.wrapping_sub(&b), U256([1, 0, 0, 0]));

        let a = U256::ZERO;
        let b = U256([1, 0, 0, 0]);
        assert_eq!(a.wrapping_sub(&b), U256::MAX);
    }

    #[test]
    fn test_xor_safe() {
        let a = U256([1, 2, 3, 4]);
        let b = U256([5, 6, 7, 8]);
        assert_eq!(a.xor_safe(&b), U256([4, 4, 4, 12]));
    }
}
