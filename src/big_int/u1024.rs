use std::fmt;
use std::ops::{Add, BitXor, Mul, Sub};

#[cfg(feature = "gmp")]
use libc::c_long;

#[cfg(feature = "avx2")]
use crate::avx2;

#[cfg(feature = "gmp")]
use crate::big_int::backend::gmp;

#[cfg(not(feature = "gmp"))]
use crate::native;

use crate::traits::BigInt;

pub(crate) const LIMBS: usize = 16;

#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct U1024(pub [u64; LIMBS]);

impl U1024 {
    pub fn from_hex(hex: &str) -> Self {
        let hex = hex.trim_start_matches("0x");
        assert!(hex.len() <= 256, "Hex string too long for U1024");

        let mut res = U1024::zero();
        let mut limb_idx = 0;
        let mut char_idx = hex.len();

        while char_idx > 0 {
            let start = char_idx.saturating_sub(16);
            let chunk = &hex[start..char_idx];

            let val = u64::from_str_radix(chunk, 16).expect("Invalid hex character");

            if limb_idx < LIMBS {
                res.0[limb_idx] = val;
            }
            limb_idx += 1;
            char_idx = start;
        }
        res
    }

    #[cfg(feature = "gmp")]
    #[inline(always)]
    fn gmp_add(&self, rhs: &Self) -> (Self, bool) {
        let mut result = U1024([0; LIMBS]);
        unsafe {
            let carry = gmp::__gmpn_add_n(
                result.0.as_mut_ptr(),
                self.0.as_ptr(),
                rhs.0.as_ptr(),
                LIMBS as c_long,
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
                LIMBS as c_long,
            );
            (result, borrow != 0)
        }
    }

    pub fn full_mul(&self, rhs: &Self) -> (Self, Self) {
        #[cfg(feature = "gmp")]
        {
            let mut res_buffer = [0u64; LIMBS * 2];

            unsafe {
                gmp::__gmpn_mul_n(
                    res_buffer.as_mut_ptr(),
                    self.0.as_ptr(),
                    rhs.0.as_ptr(),
                    LIMBS as c_long,
                );
            }

            let mut low = U1024([0; LIMBS]);
            let mut high = U1024([0; LIMBS]);

            low.0.copy_from_slice(&res_buffer[0..LIMBS]);
            high.0.copy_from_slice(&res_buffer[LIMBS..LIMBS * 2]);

            (low, high)
        }

        #[cfg(not(feature = "gmp"))]
        native::mul(self, rhs)
    }

    pub fn div_rem(&self, _modulus: &Self) -> (Self, Self) {
        #[cfg(feature = "gmp")]
        {
            let mut dn = LIMBS;
            while dn > 0 && _modulus.0[dn - 1] == 0 {
                dn -= 1;
            }

            if dn == 0 {
                panic!("Division by zero in U1024::div_rem");
            }

            let mut nn = LIMBS;
            while nn > 0 && self.0[nn - 1] == 0 {
                nn -= 1;
            }

            if nn == 0 {
                return (U1024::zero(), U1024::zero());
            }

            if nn < dn {
                return (U1024::zero(), *self);
            }

            let mut q = U1024::zero();
            let mut r = U1024::zero();

            unsafe {
                gmp::__gmpn_tdiv_qr(
                    q.0.as_mut_ptr(),
                    r.0.as_mut_ptr(),
                    0,
                    self.0.as_ptr(),
                    nn as c_long,
                    _modulus.0.as_ptr(),
                    dn as c_long,
                );
            }
            (q, r)
        }

        #[cfg(not(feature = "gmp"))]
        unimplemented!("U1024::div_rem requires the gmp feature");
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
        return native::add(self, rhs);
    }

    fn borrowing_sub(&self, rhs: &Self) -> (Self, bool) {
        #[cfg(feature = "gmp")]
        return self.gmp_sub(rhs);

        #[cfg(not(feature = "gmp"))]
        return native::sub(self, rhs);
    }

    fn conditional_select(a: &Self, b: &Self, choice: bool) -> Self {
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        #[cfg(feature = "avx2")]
        {
            if is_x86_feature_detected!("avx2") {
                unsafe {
                    return avx2::conditional_select(a, b, choice);
                }
            }
        }

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
    fn bitxor(self, rhs: Self) -> Self {
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        #[cfg(feature = "avx2")]
        {
            if is_x86_feature_detected!("avx2") {
                unsafe {
                    return avx2::xor(&self, &rhs);
                }
            }
        }

        // Native XOR
        let mut res = U1024::zero();
        for i in 0..LIMBS {
            res.0[i] = self.0[i] ^ rhs.0[i];
        }
        res
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
