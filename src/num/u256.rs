use std::ops::{Add, BitXor, Sub};

#[repr(align(32))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct U256(pub [u64; 4]);

impl U256 {
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
