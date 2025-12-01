use std::fmt;
use std::ops::{Add, BitXor, Mul, Sub};

#[cfg(feature = "gmp")]
use libc::c_ulong;

#[cfg(feature = "gmp")]
use crate::big_int::backend::gmp;
use crate::traits::BigInt;

const LIMBS: usize = 16;

#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct U1024(pub [u64; LIMBS]);

impl U1024 {
    #[cfg(feature = "gmp")]
    #[inline(always)]
    fn gmp_add(&self, rhs: &Self) -> (Self, bool) {
        let mut result = U1024([0; LIMBS]);
        unsafe {
            let carry = gmp::__gmpn_add_n(
                result.0.as_mut_ptr(),
                self.0.as_ptr(),
                rhs.0.as_ptr(),
                LIMBS as c_ulong,
            );
            (result, carry != 0)
        }
    }

    #[cfg(feature = "gmp")]
    #[inline(always)]
    fn gmp_sub(&self, rhs: &Self) -> (Self, bool) {
        let mut result = U1024([0; LIMBS]);
        unsafe {
            let borrow = gmp::__gmpn_sub_n(
                result.0.as_mut_ptr(),
                self.0.as_ptr(),
                rhs.0.as_ptr(),
                LIMBS as c_ulong,
            );
            (result, borrow != 0)
        }
    }

    pub fn full_mul(&self, rhs: &Self) -> (Self, Self) {
        let mut res_buffer = [0u64; LIMBS * 2];

        unsafe {
            #[cfg(feature = "gmp")]
            gmp::__gmpn_mul_n(
                res_buffer.as_mut_ptr(),
                self.0.as_ptr(),
                rhs.0.as_ptr(),
                LIMBS as c_ulong,
            );
        }

        let mut low = U1024([0; LIMBS]);
        let mut high = U1024([0; LIMBS]);

        low.0.copy_from_slice(&res_buffer[0..LIMBS]);
        high.0.copy_from_slice(&res_buffer[LIMBS..LIMBS * 2]);

        (low, high)
    }

    pub fn div_rem(&self, modulus: &Self) -> (Self, Self) {
        let mut q = U1024::zero();
        let mut r = U1024::zero();

        unsafe {
            #[cfg(feature = "gmp")]
            gmp::__gmpn_tdiv_qr(
                q.0.as_mut_ptr(),
                r.0.as_mut_ptr(),
                0,
                self.0.as_ptr(),
                LIMBS as c_ulong,
                modulus.0.as_ptr(),
                LIMBS as c_ulong,
            );
        }
        (q, r)
    }
}

impl BigInt for U1024 {
    const NUM_LIMBS: usize = LIMBS;

    fn zero() -> Self {
        U1024([0; LIMBS])
    }

    fn one() -> Self {
        let mut v = [0; LIMBS];
        v[0] = 1;
        U1024(v)
    }

    fn from_u64(v: u64) -> Self {
        let mut arr = [0; LIMBS];
        arr[0] = v;
        U1024(arr)
    }

    fn carrying_add(&self, rhs: &Self) -> (Self, bool) {
        #[cfg(feature = "gmp")]
        return self.gmp_add(rhs);

        #[cfg(not(feature = "gmp"))]
        unimplemented!("Native rust backend not implemented yet");
    }

    fn borrowing_sub(&self, rhs: &Self) -> (Self, bool) {
        #[cfg(feature = "gmp")]
        return self.gmp_sub(rhs);

        #[cfg(not(feature = "gmp"))]
        unimplemented!("Native rust backend not implemented yet");
    }

    fn conditional_select(a: &Self, b: &Self, choice: bool) -> Self {
        let mut res = U1024([0; LIMBS]);
        let mask = if choice { u64::MAX } else { 0 };
        for i in 0..LIMBS {
            res.0[i] = (a.0[i] & mask) | (b.0[i] & !mask);
        }
        res
    }
}

impl Add for U1024 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        self.carrying_add(&rhs).0
    }
}

impl Sub for U1024 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        self.borrowing_sub(&rhs).0
    }
}

impl Mul for U1024 {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        let (low, _) = self.full_mul(&rhs);
        low
    }
}

impl BitXor for U1024 {
    type Output = Self;
    fn bitxor(self, _rhs: Self) -> Self {
        unimplemented!("BitXor implemented in Day 4")
    }
}

impl Default for U1024 {
    fn default() -> Self {
        Self::zero()
    }
}
impl fmt::Debug for U1024 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "0x")?;
        for limb in self.0.iter().rev() {
            write!(f, "{:016x}", limb)?;
        }
        Ok(())
    }
}
impl fmt::Display for U1024 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}
