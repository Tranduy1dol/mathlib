use std::ops::{BitAnd, Shl, Shr};

use crate::num::u256::U256;

#[repr(align(32))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct U512(pub [u64; 8]);

impl U512 {
    pub const ZERO: Self = Self([0; 8]);

    pub fn get_bit(&self, bit: usize) -> bool {
        if bit >= 512 {
            false
        } else {
            (self.0[bit / 64] >> (bit % 64)) & 1 == 1
        }
    }

    pub fn set_bit(&mut self, bit: usize) {
        if bit < 512 {
            self.0[bit / 64] |= 1 << (bit % 64);
        }
    }

    pub fn div_rem(&self, divisor: &U256) -> (Self, U256) {
        let mut quotient = U512::ZERO;
        let mut remainder = U256::ZERO;

        for i in (0..512).rev() {
            remainder = remainder << 1;
            if self.get_bit(i) {
                remainder.0[0] |= 1;
            }

            if remainder.borrowing_sub(divisor).1 == false || remainder == *divisor {
                remainder = remainder.wrapping_sub(divisor);
                quotient.set_bit(i);
            }
        }
        (quotient, remainder)
    }
}

impl Shl<usize> for U512 {
    type Output = Self;

    fn shl(self, rhs: usize) -> Self::Output {
        let mut result = U512::ZERO;
        let word_shift = rhs / 64;
        let bit_shift = rhs % 64;

        for i in word_shift..8 {
            result.0[i] = self.0[i - word_shift] << bit_shift;
            if bit_shift > 0 && i > word_shift {
                result.0[i] |= self.0[i - word_shift - 1] >> (64 - bit_shift);
            }
        }
        result
    }
}

impl Shr<usize> for U512 {
    type Output = Self;

    fn shr(self, rhs: usize) -> Self::Output {
        let mut result = U512::ZERO;
        let word_shift = rhs / 64;
        let bit_shift = rhs % 64;

        for i in 0..(8 - word_shift) {
            result.0[i] = self.0[i + word_shift] >> bit_shift;
            if bit_shift > 0 && i < (7 - word_shift) {
                result.0[i] |= self.0[i + word_shift + 1] << (64 - bit_shift);
            }
        }
        result
    }
}

impl BitAnd for U512 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        let mut result = U512::ZERO;
        for i in 0..8 {
            result.0[i] = self.0[i] & rhs.0[i];
        }
        result
    }
}
