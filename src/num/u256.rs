use std::{
    fmt::{Display, Formatter},
    ops::{Add, BitXor, Mul, Shl, Sub},
};

use crate::num::{u128::U128, u512::U512};

#[repr(align(32))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct U256(pub [u64; 4]);

impl U256 {
    pub const ZERO: Self = Self([0; 4]);
    pub const MAX: Self = Self([u64::MAX; 4]);

    pub fn to_hex(&self) -> String {
        if *self == U256::ZERO {
            return "0x0".to_string();
        }

        let mut s = "0x".to_string();
        let mut leading_zeros = true;
        for &limb in self.0.iter().rev() {
            if limb == 0 && leading_zeros {
                continue;
            }

            if leading_zeros {
                s.push_str(&format!("{:x}", limb));
                leading_zeros = false;
            } else {
                s.push_str(&format!("{:016x}", limb));
            }
        }
        s
    }

    pub fn from_hex(s: &str) -> Result<Self, &'static str> {
        let s = s.strip_prefix("0x").unwrap_or(s);
        if s.len() > 64 {
            return Err("hex string is too long");
        }

        let mut limbs = [0u64; 4];
        let mut s_index = s.len();
        let mut limb_index = 0;

        while s_index > 0 {
            if limb_index > 3 {
                return Err("hex string is too long");
            }
            let start = s_index.saturating_sub(16);
            let chunk = &s[start..s_index];
            let limb = u64::from_str_radix(chunk, 16).map_err(|_| "invalid hex character")?;
            limbs[limb_index] = limb;

            limb_index += 1;
            s_index = start;
        }

        Ok(U256(limbs))
    }

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

    fn div_rem(&self, divisor: u64) -> (Self, u64) {
        if divisor == 0 {
            panic!("division by zero");
        }
        let mut rem = 0u128;
        let mut quotient = U256::ZERO;

        for i in (0..4).rev() {
            rem = (rem << 64) | (self.0[i] as u128);
            quotient.0[i] = (rem / divisor as u128) as u64;
            rem %= divisor as u128;
        }

        (quotient, rem as u64)
    }
}

impl Display for U256 {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if *self == U256::ZERO {
            return write!(f, "0");
        }

        let mut s = String::new();
        let mut current = *self;
        while current != U256::ZERO {
            let (next, rem) = current.div_rem(10);
            s.push_str(&rem.to_string());
            current = next;
        }
        write!(f, "{}", s.chars().rev().collect::<String>())
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

impl Shl<usize> for U256 {
    type Output = Self;

    fn shl(self, rhs: usize) -> Self::Output {
        let mut result = U256::ZERO;
        let word_shift = rhs / 64;
        let bit_shift = rhs % 64;

        for i in word_shift..4 {
            result.0[i] = self.0[i - word_shift] << bit_shift;
            if bit_shift > 0 && i > word_shift {
                result.0[i] |= self.0[i - word_shift - 1] >> (64 - bit_shift);
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_hex() {
        assert_eq!(U256::ZERO.to_hex(), "0x0");
        assert_eq!(U256([1, 0, 0, 0]).to_hex(), "0x1");
        assert_eq!(
            U256([0, 0, 0, 1]).to_hex(),
            "0x1000000000000000000000000000000000000000000000000"
        );
        assert_eq!(
            U256::MAX.to_hex(),
            "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
        );
    }

    #[test]
    fn test_from_hex() {
        assert_eq!(U256::from_hex("0x0").unwrap(), U256::ZERO);
        assert_eq!(U256::from_hex("1").unwrap(), U256([1, 0, 0, 0]));
        assert_eq!(
            U256::from_hex("1000000000000000000000000000000000000000000000000").unwrap(),
            U256([0, 0, 0, 1])
        );
        assert_eq!(
            U256::from_hex("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")
                .unwrap(),
            U256::MAX
        );
        assert!(U256::from_hex("1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").is_err());
        assert!(U256::from_hex("invalid").is_err());
    }

    #[test]
    fn test_display() {
        assert_eq!(U256::ZERO.to_string(), "0");
        assert_eq!(U256([1, 0, 0, 0]).to_string(), "1");
        assert_eq!(
            U256::MAX.to_string(),
            "115792089237316195423570985008687907853269984665640564039457584007913129639935"
        );
    }

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
