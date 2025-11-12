use std::ops::{Add, BitXor, Mul, Sub};

use crate::core::int::BigInt;
use crate::num::int::{u128::U128, u512::U512};

#[repr(align(32))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct U256(pub [u32; 8]);

impl BigInt for U256 {
    const ZERO: Self = Self([0; 8]);
    const ONE: Self = Self([1, 0, 0, 0, 0, 0, 0, 0]);

    #[inline]
    fn carrying_add(&self, rhs: &Self) -> (Self, bool) {
        let mut result = Self::ZERO;
        let mut carry: u64 = 0; // Cờ nhớ là u64

        for i in 0..8 {
            let sum = (self.0[i] as u64) + (rhs.0[i] as u64) + carry;
            result.0[i] = sum as u32;
            carry = sum >> 32;
        }
        (result, carry != 0)
    }

    #[inline]
    fn borrowing_sub(&self, rhs: &Self) -> (Self, bool) {
        let mut result = Self::ZERO;
        let mut borrow: i64 = 0;

        for i in 0..8 {
            // (a[i] - b[i] - borrow)
            let diff = (self.0[i] as i64) - (rhs.0[i] as i64) - borrow;
            result.0[i] = diff as u32;
            borrow = (diff >> 32) & 1;
        }
        (result, borrow != 0)
    }

    fn conditional_select(a: &Self, b: &Self, condition: bool) -> Self {
        let mask_val = if condition { u32::MAX } else { 0 };
        let mask = Self([mask_val; 8]);

        #[cfg(target_arch = "x86_64")]
        if is_x86_feature_detected!("avx2") {
            return unsafe { crate::arch::x86_64::avx2::u256_conditional_select_avx2(a, b, &mask) };
        }

        let mut result = Self::ZERO;
        for i in 0..8 {
            result.0[i] = (a.0[i] & mask.0[i]) | (b.0[i] & !mask.0[i]);
        }
        result
    }
}

impl U256 {
    pub fn full_mul_schoolbook_safe(&self, rhs: &Self) -> U512 {
        let mut result = U512::ZERO;
        for i in 0..8 {
            let a_limb = self.0[i] as u64;
            if a_limb == 0 {
                continue;
            }
            let mut carry: u64 = 0;
            for j in 0..8 {
                let product = a_limb * (rhs.0[j] as u64);
                let sum = product + (result.0[i + j] as u64);
                let sum_with_carry = sum + carry;
                result.0[i + j] = sum_with_carry as u32;
                carry = sum_with_carry >> 32;
            }

            let (res, c) = result.0[i + 8].overflowing_add(carry as u32);
            result.0[i + 8] = res;

            let mut k = i + 9;
            let mut carry_u32 = c as u32;
            while carry_u32 != 0 && k < 16 {
                let (res_k, c_k) = result.0[k].overflowing_add(carry_u32);
                result.0[k] = res_k;
                carry_u32 = c_k as u32;
                k += 1;
            }
        }
        result
    }

    pub fn mul_karatsuba(&self, rhs: &Self) -> U512 {
        let a_low = U128([self.0[0], self.0[1], self.0[2], self.0[3]]);
        let a_high = U128([self.0[4], self.0[5], self.0[6], self.0[7]]);
        let b_low = U128([rhs.0[0], rhs.0[1], rhs.0[2], rhs.0[3]]);
        let b_high = U128([rhs.0[4], rhs.0[5], rhs.0[6], rhs.0[7]]);

        // Compute the three products
        let z0 = a_low.full_mul(&b_low);   // Low part
        let z2 = a_high.full_mul(&b_high); // High part

        // Compute (a_low + a_high) * (b_low + b_high)
        let (a_sum, a_overflow) = a_low.carrying_add(&a_high);
        let (b_sum, b_overflow) = b_low.carrying_add(&b_high);
        let z1_temp = a_sum.full_mul(&b_sum);

        // Compute z1 = z1_temp - z0 - z2
        let (z1_minus_z0, borrow1) = z1_temp.borrowing_sub(&z0);
        let (z1, borrow2) = z1_minus_z0.borrowing_sub(&z2);

        // Start building result: result = z0
        let mut result = U512::ZERO;
        for i in 0..8 {
            result.0[i] = z0.0[i];
        }

        // Add z2 shifted left by 256 bits (at position 8)
        for i in 0..8 {
            result.0[i + 8] = z2.0[i];
        }

        // Add z1 shifted left by 128 bits (at position 4)
        let mut carry: u64 = 0;
        for i in 0..8 {
            let sum = (result.0[i + 4] as u64) + (z1.0[i] as u64) + carry;
            result.0[i + 4] = sum as u32;
            carry = sum >> 32;
        }

        // Propagate final carry from z1
        if carry != 0 {
            let mut i = 12;
            let mut c = carry as u32;
            while c != 0 && i < 16 {
                let sum = (result.0[i] as u64) + (c as u64);
                result.0[i] = sum as u32;
                c = (sum >> 32) as u32;
                i += 1;
            }
        }

        // Handle borrow from z1 computation (subtract from position 12)
        let total_borrow = (borrow1 as u64) + (borrow2 as u64);
        if total_borrow != 0 {
            let mut i = 12;
            let mut b = total_borrow;
            while b != 0 && i < 16 {
                let current = result.0[i] as u64;
                if current >= b {
                    result.0[i] = (current - b) as u32;
                    break;
                } else {
                    result.0[i] = (current + (1u64 << 32) - b) as u32;
                    b = 1;
                    i += 1;
                }
            }
        }

        // Handle correction terms when there were overflows in the sums
        if a_overflow {
            // Add b_sum shifted by 128 bits
            let mut carry: u64 = 0;
            for i in 0..4 {
                let sum = (result.0[i + 4] as u64) + (b_sum.0[i] as u64) + carry;
                result.0[i + 4] = sum as u32;
                carry = sum >> 32;
            }
            if carry != 0 {
                let mut i = 8;
                let mut c = carry as u32;
                while c != 0 && i < 16 {
                    let sum = (result.0[i] as u64) + (c as u64);
                    result.0[i] = sum as u32;
                    c = (sum >> 32) as u32;
                    i += 1;
                }
            }
        }

        if b_overflow {
            // Add a_sum shifted by 128 bits
            let mut carry: u64 = 0;
            for i in 0..4 {
                let sum = (result.0[i + 4] as u64) + (a_sum.0[i] as u64) + carry;
                result.0[i + 4] = sum as u32;
                carry = sum >> 32;
            }
            if carry != 0 {
                let mut i = 8;
                let mut c = carry as u32;
                while c != 0 && i < 16 {
                    let sum = (result.0[i] as u64) + (c as u64);
                    result.0[i] = sum as u32;
                    c = (sum >> 32) as u32;
                    i += 1;
                }
            }
        }

        if a_overflow && b_overflow {
            // Add 1 shifted by 256 bits (at position 8)
            let mut carry = 1u32;
            let mut i = 8;
            while carry != 0 && i < 16 {
                let sum = (result.0[i] as u64) + (carry as u64);
                result.0[i] = sum as u32;
                carry = (sum >> 32) as u32;
                i += 1;
            }
        }

        result
    }

    #[inline]
    pub fn full_mul(&self, rhs: &Self) -> U512 {
        self.full_mul_schoolbook_safe(rhs)
    }
}

impl Mul for U256 {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        let full_result = self.full_mul(&rhs);
        let mut limbs = [0u32; 8];
        limbs.copy_from_slice(&full_result.0[0..8]);
        Self(limbs)
    }
}

impl BitXor for U256 {
    type Output = Self;

    #[inline]
    fn bitxor(self, rhs: Self) -> Self::Output {
        #[cfg(target_arch = "x86_64")]
        {
            static HAS_AVX2: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            let has_avx2 = *HAS_AVX2.get_or_init(|| is_x86_feature_detected!("avx2"));

            if has_avx2 {
                return unsafe { crate::arch::x86_64::avx2::u256_xor_avx2(&self, &rhs) };
            }
        }

        let mut result = Self::ZERO;
        for i in 0..8 {
            result.0[i] = self.0[i] ^ rhs.0[i];
        }
        result
    }
}

impl Add for U256 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        self.carrying_add(&rhs).0
    }
}

impl<'b> Add<&'b U256> for &U256 {
    type Output = U256;

    fn add(self, rhs: &'b U256) -> Self::Output {
        self.carrying_add(rhs).0
    }
}

impl Sub for U256 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.borrowing_sub(&rhs).0
    }
}

impl<'b> Sub<&'b U256> for &U256 {
    type Output = U256;

    fn sub(self, rhs: &'b U256) -> Self::Output {
        self.borrowing_sub(rhs).0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper to create a U256 from a single u64 value.
    fn from_u64(val: u64) -> U256 {
        let mut limbs = [0; 8];
        limbs[0] = val as u32;
        limbs[1] = (val >> 32) as u32;
        U256(limbs)
    }

    #[test]
    fn test_constants() {
        assert_eq!(U256::ZERO, from_u64(0));
        assert_eq!(U256::ONE, from_u64(1));
    }

    #[test]
    fn test_carrying_add() {
        // Simple case: 5 + 10 = 15
        let a = from_u64(5);
        let b = from_u64(10);
        let (result, carry) = a.carrying_add(&b);
        assert_eq!(result, from_u64(15));
        assert!(!carry);

        // Addition with carry between limbs
        let a = from_u64(u32::MAX as u64);
        let b = from_u64(1);
        let (result, carry) = a.carrying_add(&b);
        assert_eq!(result, from_u64(1 << 32));
        assert!(!carry);

        // Addition that overflows the U256
        let max = U256([u32::MAX; 8]);
        let one = U256::ONE;
        let (result, carry) = max.carrying_add(&one);
        assert_eq!(result, U256::ZERO);
        assert!(carry);

        let c = from_u64(100);
        let d = from_u64(200);
        assert_eq!(&c + &d, from_u64(300));
    }

    #[test]
    fn test_carrying_add_large() {
        // Test carry propagation across multiple limbs
        let a = U256([u32::MAX, u32::MAX, 0, 0, 0, 0, 0, 0]);
        let b = from_u64(1);
        let (result, carry) = a.carrying_add(&b);
        assert_eq!(result.0[0], 0);
        assert_eq!(result.0[1], 0);
        assert_eq!(result.0[2], 1);
        assert!(!carry);

        // Test addition with values in higher limbs
        let a = U256([0, 0, 0, 0, u32::MAX, u32::MAX, u32::MAX, u32::MAX]);
        let b = U256([0, 0, 0, 0, 1, 0, 0, 0]);
        let (result, carry) = a.carrying_add(&b);
        assert_eq!(result.0[4], 0);
        assert_eq!(result.0[5], 0);
        assert_eq!(result.0[6], 0);
        assert_eq!(result.0[7], 0);
        assert!(carry);
    }

    #[test]
    fn test_borrowing_sub() {
        // Simple case: 15 - 10 = 5
        let a = from_u64(15);
        let b = from_u64(10);
        let (result, borrow) = a.borrowing_sub(&b);
        assert_eq!(result, from_u64(5));
        assert!(!borrow);

        // Subtraction with borrow between limbs
        let a = from_u64(1 << 32);
        let b = from_u64(1);
        let (result, borrow) = a.borrowing_sub(&b);
        assert_eq!(result, from_u64(u32::MAX as u64));
        assert!(!borrow);

        let zero = U256::ZERO;
        let one = U256::ONE;
        let (result, borrow) = zero.borrowing_sub(&one);
        assert_eq!(result, U256([u32::MAX; 8]));
        assert!(borrow);

        // Subtracting a number from itself
        let a = from_u64(123456789);
        let (result, borrow) = a.borrowing_sub(&a);
        assert_eq!(result, U256::ZERO);
        assert!(!borrow);

        // Sub with reference operator
        let c = from_u64(300);
        let d = from_u64(200);
        assert_eq!(&c - &d, from_u64(100));
    }

    #[test]
    fn test_borrowing_sub_large() {
        // Test borrow propagation across multiple limbs
        let a = U256([0, 0, 1, 0, 0, 0, 0, 0]);
        let b = from_u64(1);
        let (result, borrow) = a.borrowing_sub(&b);
        assert_eq!(result.0[0], u32::MAX);
        assert_eq!(result.0[1], u32::MAX);
        assert_eq!(result.0[2], 0);
        assert!(!borrow);

        // Test subtraction in higher limbs
        let a = U256([0, 0, 0, 0, 100, 0, 0, 0]);
        let b = U256([0, 0, 0, 0, 50, 0, 0, 0]);
        let (result, borrow) = a.borrowing_sub(&b);
        assert_eq!(result.0[4], 50);
        assert!(!borrow);
    }

    #[test]
    fn test_conditional_select() {
        let a = from_u64(0x_DEAD_BEEF_CAFE_BABE);
        let b = from_u64(0x_1234_5678_9ABC_DEF0);

        let result_true = U256::conditional_select(&a, &b, true);
        assert_eq!(result_true, a);

        let result_false = U256::conditional_select(&a, &b, false);
        assert_eq!(result_false, b);

        // Test with complex values
        let a = U256([1, 2, 3, 4, 5, 6, 7, 8]);
        let b = U256([8, 7, 6, 5, 4, 3, 2, 1]);

        let result_true = U256::conditional_select(&a, &b, true);
        assert_eq!(result_true, a);

        let result_false = U256::conditional_select(&a, &b, false);
        assert_eq!(result_false, b);
    }

    #[test]
    fn test_add_operator() {
        let a = from_u64(100);
        let b = from_u64(50);
        assert_eq!(a + b, from_u64(150));

        // Test with zero
        let a = from_u64(42);
        let zero = U256::ZERO;
        assert_eq!(a + zero, a);

        // Test commutativity
        let a = from_u64(123);
        let b = from_u64(456);
        assert_eq!(a + b, b + a);
    }

    #[test]
    fn test_sub_operator() {
        let a = from_u64(100);
        let b = from_u64(50);
        assert_eq!(a - b, from_u64(50));

        // Test subtracting zero
        let a = from_u64(42);
        let zero = U256::ZERO;
        assert_eq!(a - zero, a);

        // Test subtracting from itself
        let a = from_u64(999);
        assert_eq!(a - a, U256::ZERO);
    }

    #[test]
    fn test_xor_operator() {
        // Simple XOR
        let a = from_u64(0b1010);
        let b = from_u64(0b1100);
        let expected = from_u64(0b0110);
        assert_eq!(a ^ b, expected);

        // XOR with zero (identity)
        let a = from_u64(0x_DEADBEEF);
        let zero = U256::ZERO;
        assert_eq!(a ^ zero, a);

        // XOR with itself (should be zero)
        let a = from_u64(0x_12345678);
        assert_eq!(a ^ a, U256::ZERO);

        // XOR is commutative
        let a = U256([1, 2, 3, 4, 5, 6, 7, 8]);
        let b = U256([8, 7, 6, 5, 4, 3, 2, 1]);
        assert_eq!(a ^ b, b ^ a);
    }

    #[test]
    fn test_mul_operator_small() {
        // Simple multiplication
        let a = from_u64(10);
        let b = from_u64(20);
        assert_eq!(a * b, from_u64(200));

        // Multiplication with zero
        let a = from_u64(42);
        let zero = U256::ZERO;
        assert_eq!(a * zero, U256::ZERO);

        // Multiplication with one
        let a = from_u64(12345);
        let one = U256::ONE;
        assert_eq!(a * one, a);

        // Commutativity
        let a = from_u64(7);
        let b = from_u64(13);
        assert_eq!(a * b, b * a);
    }

    #[test]
    fn test_mul_operator_overflow() {
        // Multiplication that overflows (takes lower 256 bits)
        let a = U256([u32::MAX, u32::MAX, 0, 0, 0, 0, 0, 0]);
        let b = from_u64(2);
        let result = a * b;
        // 2^64 - 1 * 2 = 2^65 - 2, lower 256 bits = 2^64 - 2
        assert_eq!(result.0[0], u32::MAX - 1);
        assert_eq!(result.0[1], u32::MAX);
        assert_eq!(result.0[2], 1);
    }

    #[test]
    fn test_full_mul_schoolbook_small() {
        // Simple case: 10 * 20 = 200
        let a = from_u64(10);
        let b = from_u64(20);
        let result = a.full_mul_schoolbook_safe(&b);
        assert_eq!(result.0[0], 200);
        assert_eq!(result.0[1], 0);

        // Multiplication with zero
        let a = from_u64(12345);
        let zero = U256::ZERO;
        let result = a.full_mul_schoolbook_safe(&zero);
        assert_eq!(result, U512::ZERO);

        // Multiplication with one
        let a = from_u64(99999);
        let one = U256::ONE;
        let result = a.full_mul_schoolbook_safe(&one);
        assert_eq!(result.0[0], 99999);
        for i in 1..16 {
            assert_eq!(result.0[i], 0);
        }
    }

    #[test]
    fn test_full_mul_schoolbook_large() {
        // Test with large values
        let a = U256([u32::MAX, u32::MAX, 0, 0, 0, 0, 0, 0]);
        let b = U256([u32::MAX, u32::MAX, 0, 0, 0, 0, 0, 0]);
        let result = a.full_mul_schoolbook_safe(&b);

        // (2^64 - 1)^2 = 2^128 - 2^65 + 1
        assert_eq!(result.0[0], 1);
        assert_eq!(result.0[1], 0);
        assert_eq!(result.0[2], u32::MAX - 1);
        assert_eq!(result.0[3], u32::MAX);

        // Commutativity test
        let a = U256([1, 2, 3, 4, 5, 6, 7, 8]);
        let b = U256([8, 7, 6, 5, 4, 3, 2, 1]);
        assert_eq!(
            a.full_mul_schoolbook_safe(&b),
            b.full_mul_schoolbook_safe(&a)
        );
    }

    #[test]
    fn test_full_mul_karatsuba_small() {
        // Simple case
        let a = from_u64(10);
        let b = from_u64(20);
        let result = a.mul_karatsuba(&b);
        assert_eq!(result.0[0], 200);
        assert_eq!(result.0[1], 0);

        // Multiplication with zero
        let a = from_u64(12345);
        let zero = U256::ZERO;
        let result = a.mul_karatsuba(&zero);
        assert_eq!(result, U512::ZERO);

        // Multiplication with one
        let a = from_u64(99999);
        let one = U256::ONE;
        let result = a.mul_karatsuba(&one);
        assert_eq!(result.0[0], 99999);
        for i in 1..16 {
            assert_eq!(result.0[i], 0);
        }
    }

    #[test]
    fn test_full_mul_karatsuba_vs_schoolbook() {
        // Test that Karatsuba and Schoolbook produce the same results
        let test_cases = vec![
            (from_u64(0), from_u64(0)),
            (from_u64(1), from_u64(1)),
            (from_u64(100), from_u64(200)),
            (from_u64(u32::MAX as u64), from_u64(u32::MAX as u64)),
            (
                U256([u32::MAX, u32::MAX, 0, 0, 0, 0, 0, 0]),
                U256([u32::MAX, u32::MAX, 0, 0, 0, 0, 0, 0]),
            ),
            (
                U256([1, 2, 3, 4, 5, 6, 7, 8]),
                U256([8, 7, 6, 5, 4, 3, 2, 1]),
            ),
            (
                U256([u32::MAX, 0, u32::MAX, 0, u32::MAX, 0, u32::MAX, 0]),
                U256([0, u32::MAX, 0, u32::MAX, 0, u32::MAX, 0, u32::MAX]),
            ),
            (
                U256([
                    0x12345678, 0x9ABCDEF0, 0xFEDCBA98, 0x76543210, 0x11111111, 0x22222222,
                    0x33333333, 0x44444444,
                ]),
                U256([
                    0x55555555, 0x66666666, 0x77777777, 0x88888888, 0x99999999, 0xAAAAAAAA,
                    0xBBBBBBBB, 0xCCCCCCCC,
                ]),
            ),
        ];

        for (a, b) in test_cases {
            let schoolbook_result = a.full_mul_schoolbook_safe(&b);
            let karatsuba_result = a.mul_karatsuba(&b);
            assert_eq!(
                schoolbook_result, karatsuba_result,
                "Mismatch for a={:?}, b={:?}",
                a, b
            );
        }
    }

    #[test]
    fn test_full_mul_consistency() {
        // Test that full_mul (wrapper) is consistent with implementation
        let a = U256([
            0x12345678, 0x9ABCDEF0, 0xFEDCBA98, 0x76543210, 0x11111111, 0x22222222, 0x33333333,
            0x44444444,
        ]);
        let b = U256([
            0x55555555, 0x66666666, 0x77777777, 0x88888888, 0x99999999, 0xAAAAAAAA, 0xBBBBBBBB,
            0xCCCCCCCC,
        ]);

        let result1 = a.full_mul(&b);
        let result2 = a.full_mul_schoolbook_safe(&b);
        assert_eq!(result1, result2);
    }

    #[test]
    fn test_edge_cases() {
        // Test max value
        let max = U256([u32::MAX; 8]);

        // max + 0 = max
        assert_eq!(max + U256::ZERO, max);

        // max - max = 0
        assert_eq!(max - max, U256::ZERO);

        // max ^ max = 0
        assert_eq!(max ^ max, U256::ZERO);

        // max ^ 0 = max
        assert_eq!(max ^ U256::ZERO, max);
    }

    #[test]
    fn test_distributivity() {
        // Test a * (b + c) = a*b + a*c (considering only lower 256 bits)
        let a = from_u64(123);
        let b = from_u64(456);
        let c = from_u64(789);

        let left = a * (b + c);
        let right = (a * b) + (a * c);
        assert_eq!(left, right);
    }

    #[test]
    fn test_associativity() {
        // Test (a + b) + c = a + (b + c)
        let a = from_u64(100);
        let b = from_u64(200);
        let c = from_u64(300);

        assert_eq!((a + b) + c, a + (b + c));

        // Test (a * b) * c = a * (b * c) (lower 256 bits)
        let a = from_u64(5);
        let b = from_u64(7);
        let c = from_u64(11);
        assert_eq!((a * b) * c, a * (b * c));
    }

    #[test]
    fn test_copy_and_clone() {
        let a = U256([1, 2, 3, 4, 5, 6, 7, 8]);
        let b = a; // Copy
        assert_eq!(a, b);

        let c = a.clone(); // Clone
        assert_eq!(a, c);
    }

    #[test]
    fn test_debug_format() {
        let a = U256([1, 2, 3, 4, 5, 6, 7, 8]);
        let debug_str = format!("{:?}", a);
        assert!(debug_str.contains("U256"));
    }
}
