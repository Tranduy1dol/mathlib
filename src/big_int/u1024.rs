use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, BitXor, Div, Mul, Rem, Shl, Shr, Sub};

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

/// Macro to create a U1024 value from different sources.
///
/// # Examples
///
/// ```
/// use lumen_math::u1024;
///
/// // From a hex string
/// let a = u1024!("0x1234");
///
/// // From an array of u64 limbs
/// let b = u1024!([1, 2, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
///
/// // From primitive types (with type suffixes)
/// let c = u1024!(42u8);
/// let d = u1024!(1000u16);
/// let e = u1024!(100000u32);
/// let f = u1024!(123456789u64);
/// let g = u1024!(0x123456789ABCDEFu128);
/// ```
#[macro_export]
macro_rules! u1024 {
    // From array of u64 - must come first to match array syntax
    ([$($limb:expr),+ $(,)?]) => {{
        $crate::U1024([$($limb),+])
    }};
    // From hex string - strings must come before general expressions
    ($hex:expr) => {{
        // Use a helper to dispatch based on type
        #[allow(unused_imports)]
        {
            // Try to match a string type first
            #[allow(dead_code)]
            const fn is_str_type<T: ?Sized>(_: &T) -> bool {
                false
            }
            #[allow(dead_code)]
            const fn is_str_type_str(_: &&str) -> bool {
                true
            }

            // Helper trait to convert to U1024
            trait ToU1024 {
                fn to_u1024(self) -> $crate::U1024;
            }

            impl ToU1024 for &str {
                fn to_u1024(self) -> $crate::U1024 {
                    $crate::U1024::from_hex(self)
                }
            }

            impl ToU1024 for i8 {
                fn to_u1024(self) -> $crate::U1024 {
                    $crate::U1024::from_u8(self as u8)
                }
            }

            impl ToU1024 for i16 {
                fn to_u1024(self) -> $crate::U1024 {
                    $crate::U1024::from_u16(self as u16)
                }
            }

            impl ToU1024 for i32 {
                fn to_u1024(self) -> $crate::U1024 {
                    $crate::U1024::from_u32(self as u32)
                }
            }

            impl ToU1024 for i64 {
                fn to_u1024(self) -> $crate::U1024 {
                    $crate::U1024::from_u64(self as u64)
                }
            }

            impl ToU1024 for i128 {
                fn to_u1024(self) -> $crate::U1024 {
                    $crate::U1024::from_u128(self as u128)
                }
            }

            impl ToU1024 for u8 {
                fn to_u1024(self) -> $crate::U1024 {
                    $crate::U1024::from_u8(self)
                }
            }

            impl ToU1024 for u16 {
                fn to_u1024(self) -> $crate::U1024 {
                    $crate::U1024::from_u16(self)
                }
            }

            impl ToU1024 for u32 {
                fn to_u1024(self) -> $crate::U1024 {
                    $crate::U1024::from_u32(self)
                }
            }

            impl ToU1024 for u64 {
                fn to_u1024(self) -> $crate::U1024 {
                    $crate::U1024::from_u64(self)
                }
            }

            impl ToU1024 for u128 {
                fn to_u1024(self) -> $crate::U1024 {
                    $crate::U1024::from_u128(self)
                }
            }

            ToU1024::to_u1024($hex)
        }
    }};
}

#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct U1024(pub [u64; LIMBS]);

impl U1024 {
    pub const ZERO: Self = Self([0; LIMBS]);

    pub const ONE: Self = Self([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);

    /// Const-compatible equality check
    pub const fn const_eq(&self, other: &Self) -> bool {
        let mut i = 0;
        while i < LIMBS {
            if self.0[i] != other.0[i] {
                return false;
            }
            i += 1;
        }
        true
    }

    /// Const-compatible addition. Returns (result, carry).
    pub const fn const_add(&self, rhs: &Self) -> (Self, bool) {
        let mut ret = [0u64; LIMBS];
        let mut carry = 0u64;
        let mut i = 0;

        while i < LIMBS {
            let (sum1, c1) = self.0[i].overflowing_add(rhs.0[i]);
            let (sum2, c2) = sum1.overflowing_add(carry);

            ret[i] = sum2;
            carry = (c1 as u64) + (c2 as u64);
            i += 1;
        }
        (U1024(ret), carry != 0)
    }

    /// Const-compatible subtraction. Returns (result, borrow).
    pub const fn const_sub(&self, rhs: &Self) -> (Self, bool) {
        let mut ret = [0u64; LIMBS];
        let mut borrow = 0u64;
        let mut i = 0;

        while i < LIMBS {
            let (diff1, b1) = self.0[i].overflowing_sub(rhs.0[i]);
            let (diff2, b2) = diff1.overflowing_sub(borrow);

            ret[i] = diff2;
            borrow = (b1 as u64) + (b2 as u64);
            i += 1;
        }
        (U1024(ret), borrow != 0)
    }

    /// Const-compatible multiplication. Returns (low, high).
    pub const fn const_mul(&self, rhs: &Self) -> (Self, Self) {
        let mut res = [0u64; LIMBS * 2];
        let mut i = 0;

        while i < LIMBS {
            let mut carry = 0u64;
            let mut j = 0;
            while j < LIMBS {
                let k = i + j;
                let val = res[k] as u128 + (self.0[i] as u128 * rhs.0[j] as u128) + carry as u128;
                res[k] = val as u64;
                carry = (val >> 64) as u64;
                j += 1;
            }
            let mut k = i + LIMBS;
            while carry > 0 && k < LIMBS * 2 {
                let val = res[k] as u128 + carry as u128;
                res[k] = val as u64;
                carry = (val >> 64) as u64;
                k += 1;
            }
            i += 1;
        }

        let mut low = [0u64; LIMBS];
        let mut high = [0u64; LIMBS];

        let mut k = 0;
        while k < LIMBS {
            low[k] = res[k];
            high[k] = res[k + LIMBS];
            k += 1;
        }

        (U1024(low), U1024(high))
    }

    /// Report whether the bit at the given zero-based index is set.
    ///
    /// Index 0 refers to the least-significant bit of the value; valid indexes are 0 through 1023.
    /// If `index >= 1024`, the function returns `false`.
    ///
    /// # Parameters
    ///
    /// - `index`: zero-based bit index where 0 is the least-significant bit.
    ///
    /// # Returns
    ///
    /// `true` if the specified bit is 1, `false` otherwise (also `false` for indexes >= 1024).
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::u1024;
    ///
    /// let v = u1024!(0b10u64);
    /// assert!(!v.bit(0));
    /// assert!(v.bit(1));
    /// assert!(!v.bit(1024)); // out-of-range
    /// ```
    pub fn bit(&self, index: usize) -> bool {
        if index >= 1024 {
            return false;
        }

        let limb_idx = index / 64;
        let bit_idx = index % 64;

        (self.0[limb_idx] >> bit_idx) & 1 == 1
    }

    /// Compute the bit length of the value.
    ///
    /// Scans limbs from most-significant to least-significant and returns the index
    /// of the highest set bit plus one. Returns `0` if the value is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::u1024;
    ///
    /// let v = u1024!(0u64);
    /// assert_eq!(v.bits(), 0);
    ///
    /// let v = u1024!(1u64);
    /// assert_eq!(v.bits(), 1);
    ///
    /// let v = u1024!(0x10u64);
    /// assert_eq!(v.bits(), 5);
    /// ```
    pub fn bits(&self) -> usize {
        let mut result = 0usize;
        // Iterate from lowest to highest limb
        // The conditional select will keep updating with higher limbs that are non-zero
        for (i, limb) in self.0.iter().enumerate() {
            let is_nonzero = ((limb | limb.wrapping_neg()) >> 63) as usize;
            let candidate_bits = (i + 1) * 64 - limb.leading_zeros() as usize;

            let mask = 0usize.wrapping_sub(is_nonzero);
            result = (candidate_bits & mask) | (result & !mask);
        }

        result
    }

    /// Creates a U1024 value from a hexadecimal string.
    ///
    /// The function accepts an optional leading `"0x"` prefix, asserts the hex
    /// length does not exceed 256 characters (1024 bits), and parses the string in
    /// 16-hex-digit chunks from the least-significant end. Each parsed chunk is
    /// placed into successive limbs starting at the least-significant limb. Parsing
    /// fails with a panic on invalid hex characters.
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::u1024;
    ///
    /// let v = u1024!("0x01ff");
    /// assert_eq!(v.0[0], 0x01ff);
    ///
    /// let v2 = u1024!("ff0000000000000001");
    /// // The string has 18 hex digits, so it spans 2 limbs
    /// // Low limb (v2.0[0]) holds the least-significant 16 hex digits
    /// assert_eq!(v2.0[0], 0x0000000000000001);
    /// // Next limb (v2.0[1]) holds the remaining 2 hex digits
    /// assert_eq!(v2.0[1], 0xff);
    /// ```
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

    /// Creates a U1024 value from a u8.
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::u1024;
    ///
    /// let v = u1024!(42u8);
    /// assert_eq!(v.0[0], 42);
    /// ```
    pub fn from_u8(v: u8) -> Self {
        let mut arr = [0; LIMBS];
        arr[0] = v as u64;
        U1024(arr)
    }

    /// Creates a U1024 value from a u16.
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::u1024;
    ///
    /// let v = u1024!(1000u16);
    /// assert_eq!(v.0[0], 1000);
    /// ```
    pub fn from_u16(v: u16) -> Self {
        let mut arr = [0; LIMBS];
        arr[0] = v as u64;
        U1024(arr)
    }

    /// Creates a U1024 value from a u32.
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::u1024;
    ///
    /// let v = u1024!(100000u32);
    /// assert_eq!(v.0[0], 100000);
    /// ```
    pub fn from_u32(v: u32) -> Self {
        let mut arr = [0; LIMBS];
        arr[0] = v as u64;
        U1024(arr)
    }

    /// Creates a U1024 value from a u64.
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::u1024;
    ///
    /// let v = u1024!(123456789u64);
    /// assert_eq!(v.0[0], 123456789);
    /// ```
    pub fn from_u64(v: u64) -> Self {
        let mut arr = [0; LIMBS];
        arr[0] = v;
        U1024(arr)
    }

    /// Creates a U1024 value from a u128.
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::u1024;
    ///
    /// let v = u1024!(0x123456789ABCDEF0123456789ABCDEFu128);
    /// assert_eq!(v.0[0], 0x0123456789ABCDEFu64);
    /// assert_eq!(v.0[1], 0x123456789ABCDEFu64);
    /// ```
    pub fn from_u128(v: u128) -> Self {
        let mut arr = [0; LIMBS];
        arr[0] = v as u64;
        arr[1] = (v >> 64) as u64;
        U1024(arr)
    }

    /// Creates a U1024 value from a bit array (bool array).
    ///
    /// The array should have up to 1024 elements, where index 0 represents the
    /// least-significant bit. Any elements beyond index 1023 are ignored.
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::U1024;
    ///
    /// let bits = [true, false, true, true]; // Represents binary 0b1101 = 13
    /// let v = U1024::from_bits(&bits);
    /// assert_eq!(v.0[0], 0b1101);
    /// ```
    pub fn from_bits(bits: &[bool]) -> Self {
        let mut res = U1024::zero();
        for (i, &bit) in bits.iter().enumerate().take(1024) {
            if bit {
                let limb_idx = i / 64;
                let bit_idx = i % 64;
                res.0[limb_idx] |= 1u64 << bit_idx;
            }
        }
        res
    }

    /// Creates a U1024 value from a slice of bytes in little-endian order.
    ///
    /// The slice should have up to 128 bytes (1024 bits). Any additional bytes
    /// are ignored. Bytes are interpreted in little-endian order where the first
    /// byte represents the least-significant byte.
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::U1024;
    ///
    /// let bytes = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08];
    /// let v = U1024::from_le_bytes(&bytes);
    /// assert_eq!(v.0[0], 0x0807060504030201u64);
    /// ```
    pub fn from_le_bytes(bytes: &[u8]) -> Self {
        let mut res = U1024::zero();
        for (i, &byte) in bytes.iter().enumerate().take(128) {
            let limb_idx = i / 8;
            let byte_idx = i % 8;
            res.0[limb_idx] |= (byte as u64) << (byte_idx * 8);
        }
        res
    }

    /// Creates a U1024 value from a slice of bytes in big-endian order.
    ///
    /// The slice should have up to 128 bytes (1024 bits). Any additional bytes
    /// are ignored. Bytes are interpreted in big-endian order where the first
    /// byte represents the most-significant byte.
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::U1024;
    ///
    /// let bytes = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08];
    /// let v = U1024::from_be_bytes(&bytes);
    /// assert_eq!(v.0[0], 0x0102030405060708u64);
    /// ```
    pub fn from_be_bytes(bytes: &[u8]) -> Self {
        let mut res = U1024::zero();
        let n = bytes.len().min(128);
        for (i, &byte) in bytes.iter().take(n).enumerate() {
            let bit_pos = (n - 1 - i) * 8;
            let limb_idx = bit_pos / 64;
            let byte_idx = (bit_pos % 64) / 8;
            res.0[limb_idx] |= (byte as u64) << (byte_idx * 8);
        }
        res
    }

    /// Converts this U1024 value to a 128-byte array in little-endian order.
    ///
    /// The least-significant byte is at index 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::U1024;
    ///
    /// let v = U1024::from_le_bytes(&[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]);
    /// let bytes = v.to_le_bytes();
    /// assert_eq!(&bytes[..8], &[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]);
    /// ```
    pub fn to_le_bytes(&self) -> [u8; 128] {
        let mut result = [0u8; 128];
        for (i, &limb) in self.0.iter().enumerate() {
            let bytes = limb.to_le_bytes();
            let offset = i * 8;
            result[offset..offset + 8].copy_from_slice(&bytes);
        }
        result
    }

    /// Converts this U1024 value to a 128-byte array in big-endian order.
    ///
    /// The most-significant byte is at index 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::U1024;
    ///
    /// let v = U1024::from_be_bytes(&[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]);
    /// let bytes = v.to_be_bytes();
    /// // 8 bytes read as big-endian go to the high end of the buffer
    /// assert_eq!(bytes[120..128], [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]);
    /// ```
    pub fn to_be_bytes(&self) -> [u8; 128] {
        let mut result = [0u8; 128];
        for (i, &limb) in self.0.iter().enumerate() {
            let bytes = limb.to_be_bytes();
            // Limb 0 (least significant) goes to the end of the array
            let offset = (LIMBS - 1 - i) * 8;
            result[offset..offset + 8].copy_from_slice(&bytes);
        }
        result
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

    /// Left shift by `n` bits.
    ///
    /// If `n >= 1024`, returns zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::U1024;
    ///
    /// let v = U1024::from_u64(1);
    /// let shifted = v.shl(10);
    /// assert_eq!(shifted.0[0], 1024); // 2^10
    /// ```
    pub fn shl(&self, n: usize) -> Self {
        if n >= 1024 {
            return Self::ZERO;
        }

        if n == 0 {
            return *self;
        }

        let limb_shift = n / 64;
        let bit_shift = n % 64;

        let mut result = [0u64; LIMBS];

        if bit_shift == 0 {
            // Simple limb-only shift
            result[limb_shift..LIMBS].copy_from_slice(&self.0[..(LIMBS - limb_shift)]);
        } else {
            // Need to handle bit carry between limbs
            for (i, result_limb) in result.iter_mut().enumerate().skip(limb_shift) {
                let src_idx = i - limb_shift;
                *result_limb = self.0[src_idx] << bit_shift;
                if src_idx > 0 {
                    *result_limb |= self.0[src_idx - 1] >> (64 - bit_shift);
                }
            }
        }

        Self(result)
    }

    /// Right shift by `n` bits.
    ///
    /// If `n >= 1024`, returns zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::U1024;
    ///
    /// let v = U1024::from_u64(1024);
    /// let shifted = v.shr(10);
    /// assert_eq!(shifted.0[0], 1); // 1024 / 2^10 = 1
    /// ```
    pub fn shr(&self, n: usize) -> Self {
        if n >= 1024 {
            return Self::ZERO;
        }

        if n == 0 {
            return *self;
        }

        let limb_shift = n / 64;
        let bit_shift = n % 64;

        let mut result = [0u64; LIMBS];

        if bit_shift == 0 {
            // Simple limb-only shift
            result[..(LIMBS - limb_shift)].copy_from_slice(&self.0[limb_shift..LIMBS]);
        } else {
            // Need to handle bit carry between limbs
            for (i, result_limb) in result.iter_mut().enumerate().take(LIMBS - limb_shift) {
                let src_idx = i + limb_shift;
                *result_limb = self.0[src_idx] >> bit_shift;
                if src_idx + 1 < LIMBS {
                    *result_limb |= self.0[src_idx + 1] << (64 - bit_shift);
                }
            }
        }

        Self(result)
    }

    /// Returns a new U1024 with the specified bit set to 1.
    ///
    /// If `index >= 1024`, returns self unchanged.
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::U1024;
    ///
    /// let v = U1024::ZERO;
    /// let with_bit = v.with_bit(10);
    /// assert_eq!(with_bit.0[0], 1024); // 2^10
    /// ```
    pub fn with_bit(&self, index: usize) -> Self {
        if index >= 1024 {
            return *self;
        }

        let limb_idx = index / 64;
        let bit_idx = index % 64;

        let mut result = self.0;
        result[limb_idx] |= 1u64 << bit_idx;

        Self(result)
    }

    /// Division with remainder: returns (quotient, remainder) such that
    /// `self = quotient * divisor + remainder`.
    ///
    /// # Panics
    ///
    /// Panics if `divisor` is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::U1024;
    ///
    /// let a = U1024::from_u64(100);
    /// let b = U1024::from_u64(7);
    /// let (q, r) = a.div_rem(&b);
    /// assert_eq!(q, U1024::from_u64(14)); // 100 / 7 = 14
    /// assert_eq!(r, U1024::from_u64(2));  // 100 % 7 = 2
    /// ```
    pub fn div_rem(&self, divisor: &Self) -> (Self, Self) {
        #[cfg(feature = "gmp")]
        {
            let mut dn = LIMBS;
            while dn > 0 && divisor.0[dn - 1] == 0 {
                dn -= 1;
            }

            if dn == 0 {
                panic!("Division by zero");
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
                    divisor.0.as_ptr(),
                    dn as c_long,
                );
            }
            (q, r)
        }

        #[cfg(not(feature = "gmp"))]
        {
            if *divisor == Self::ZERO {
                panic!("Division by zero");
            }

            if *self < *divisor {
                return (Self::ZERO, *self);
            }

            if *self == *divisor {
                return (Self::from_u64(1), Self::ZERO);
            }

            // Binary long division
            let mut quotient = Self::ZERO;
            let mut remainder = Self::ZERO;
            let one = Self::ONE;

            for i in (0..1024).rev() {
                // Left shift remainder by 1
                remainder = remainder.shl(1);

                let bit = self.bit(i);
                let rem_plus_one = remainder + one;
                remainder = Self::conditional_select(&rem_plus_one, &remainder, bit);

                let (sub_result, borrow) = remainder.borrowing_sub(divisor);
                let should_subtract = !borrow;

                remainder = Self::conditional_select(&sub_result, &remainder, should_subtract);

                let quotient_with_bit = quotient.with_bit(i);
                quotient = Self::conditional_select(&quotient_with_bit, &quotient, should_subtract);
            }

            (quotient, remainder)
        }
    }

    /// Returns the quotient of `self / divisor`.
    ///
    /// # Panics
    ///
    /// Panics if `divisor` is zero.
    #[inline]
    pub fn checked_div(&self, divisor: &Self) -> Self {
        self.div_rem(divisor).0
    }

    /// Returns the remainder of `self % divisor`.
    ///
    /// # Panics
    ///
    /// Panics if `divisor` is zero.
    #[inline]
    pub fn checked_rem(&self, divisor: &Self) -> Self {
        self.div_rem(divisor).1
    }

    /// Modular multiplication: computes (self * other) mod modulus.
    ///
    /// Handles the case where the product exceeds 1024 bits by properly
    /// reducing the 2048-bit intermediate result.
    ///
    /// # Panics
    ///
    /// Panics if `modulus` is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::U1024;
    ///
    /// let a = U1024::from_u64(123);
    /// let b = U1024::from_u64(456);
    /// let m = U1024::from_u64(1000);
    /// let result = a.mod_mul(&b, &m);
    /// assert_eq!(result, U1024::from_u64((123 * 456) % 1000));
    /// ```
    pub fn mod_mul(&self, other: &Self, modulus: &Self) -> Self {
        if *modulus == Self::ZERO {
            panic!("Modulus cannot be zero");
        }

        let (lo, hi) = self.const_mul(other);

        // If hi is zero, we can just reduce lo
        if hi == Self::ZERO {
            return lo % *modulus;
        }

        // For a full 2048-bit product, we need to reduce properly
        // We use: (2^1024 * hi + lo) mod m = ((2^1024 mod m) * hi + lo) mod m
        let r = Self::pow2_1024_mod(modulus);
        let (hi_reduced_lo, hi_reduced_hi) = r.const_mul(&hi);

        if hi_reduced_hi != Self::ZERO {
            // Fallback for very small moduli
            let term1 = hi_reduced_lo % *modulus;
            let term2 = lo % *modulus;
            let sum = term1 + term2;
            return sum % *modulus;
        }

        let sum = lo + hi_reduced_lo;
        if sum < lo {
            // Overflow: add 2^1024 mod m
            let overflow_contrib = r % *modulus;
            let partial = sum % *modulus;
            return (partial + overflow_contrib) % *modulus;
        }

        sum % *modulus
    }

    /// Modular exponentiation: computes self^exp mod modulus.
    ///
    /// Uses the square-and-multiply (binary exponentiation) algorithm.
    /// Time complexity: O(log exp) multiplications.
    ///
    /// # Panics
    ///
    /// Panics if `modulus` is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::U1024;
    ///
    /// let base = U1024::from_u64(2);
    /// let exp = U1024::from_u64(10);
    /// let modulus = U1024::from_u64(1000);
    ///
    /// // 2^10 mod 1000 = 1024 mod 1000 = 24
    /// let result = base.mod_pow(&exp, &modulus);
    /// assert_eq!(result, U1024::from_u64(24));
    /// ```
    pub fn mod_pow(&self, exp: &Self, modulus: &Self) -> Self {
        if *modulus == Self::ZERO {
            panic!("Modulus cannot be zero");
        }

        if *modulus == Self::ONE {
            return Self::ZERO;
        }

        let mut result = Self::ONE;
        let mut base = *self % *modulus;

        // Process each bit of the exponent
        for i in 0..16 {
            let mut limb = exp.0[i];
            for _ in 0..64 {
                let bit = (limb & 1) == 1;
                let product = result.mod_mul(&base, modulus);

                result = Self::conditional_select(&product, &result, bit);
                base = base.mod_mul(&base, modulus);

                limb >>= 1;
            }
        }

        result
    }

    /// Alias for mod_pow - Cyclic Group Exponentiation.
    ///
    /// Traditional name for modular exponentiation in group theory contexts:
    /// computes g^x mod n.
    #[inline]
    pub fn cge(&self, exponent: &Self, modulus: &Self) -> Self {
        self.mod_pow(exponent, modulus)
    }

    /// Helper: compute 2^1024 mod m.
    fn pow2_1024_mod(m: &Self) -> Self {
        // 2^1024 mod m is equivalent to (2^1024 - m) mod m.
        // In U1024 arithmetic, 0 - m wraps to 2^1024 - m.
        // So we just compute (0 - m) % m.
        (Self::ZERO - *m) % *m
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
        let mask = 0u64.wrapping_sub(choice as u64);
        let mask = core::hint::black_box(mask);
        for i in 0..LIMBS {
            let a_val = core::hint::black_box(a.0[i]);
            let b_val = core::hint::black_box(b.0[i]);

            res.0[i] = (a_val & mask) | (b_val & !mask);
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

impl Div for U1024 {
    type Output = Self;
    fn div(self, rhs: Self) -> Self {
        self.checked_div(&rhs)
    }
}

impl Rem for U1024 {
    type Output = Self;
    fn rem(self, rhs: Self) -> Self {
        self.checked_rem(&rhs)
    }
}

impl Shl<usize> for U1024 {
    type Output = Self;
    fn shl(self, rhs: usize) -> Self {
        U1024::shl(&self, rhs)
    }
}

impl Shr<usize> for U1024 {
    type Output = Self;
    fn shr(self, rhs: usize) -> Self {
        U1024::shr(&self, rhs)
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

impl PartialOrd for U1024 {
    /// Compares two U1024 values.
    ///
    /// Comparison is performed from the most-significant limb to the least-significant
    /// limb, returning as soon as a difference is found.
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::u1024;
    ///
    /// let a = u1024!(100u64);
    /// let b = u1024!(200u64);
    /// assert!(a < b);
    /// assert!(b > a);
    /// assert!(a <= b);
    /// assert!(b >= a);
    /// ```
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for U1024 {
    /// Compares two U1024 values for ordering.
    ///
    /// The comparison starts from the most-significant limb (index 15) and works
    /// down to the least-significant limb (index 0). This ensures correct ordering
    /// for the little-endian limb representation.
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::u1024;
    /// use std::cmp::Ordering;
    ///
    /// let a = u1024!(100u64);
    /// let b = u1024!(200u64);
    /// assert_eq!(a.cmp(&b), Ordering::Less);
    /// assert_eq!(b.cmp(&a), Ordering::Greater);
    /// assert_eq!(a.cmp(&a), Ordering::Equal);
    /// ```
    fn cmp(&self, other: &Self) -> Ordering {
        // Compare from most-significant limb to least-significant
        for i in (0..LIMBS).rev() {
            match self.0[i].cmp(&other.0[i]) {
                Ordering::Equal => continue,
                ord => return ord,
            }
        }
        Ordering::Equal
    }
}

// Digest implementation
use crate::traits::Digest;
use sha2::{Digest as Sha2Digest, Sha256};

impl Digest for U1024 {
    fn from_hash(input: &[u8]) -> Self {
        let expanded = expand_message_sha256(input, 128);
        Self::from_be_bytes(&expanded)
    }

    fn from_hash_with_domain(domain: &[u8], input: &[u8]) -> Self {
        // Concatenate domain separator with length prefix
        let mut data = Vec::with_capacity(domain.len() + input.len() + 8);
        data.extend_from_slice(&(domain.len() as u64).to_be_bytes());
        data.extend_from_slice(domain);
        data.extend_from_slice(input);

        Self::from_hash(&data)
    }
}

/// Expands a message to the specified length using SHA256 (RFC 9380 style).
fn expand_message_sha256(input: &[u8], len_in_bytes: usize) -> Vec<u8> {
    const DST: &[u8] = b"lumen_math_expand_v1";
    const HASH_LEN: usize = 32;

    let ell = len_in_bytes.div_ceil(HASH_LEN);

    let dst_prime = {
        let mut d = Vec::with_capacity(DST.len() + 1);
        d.extend_from_slice(DST);
        d.push(DST.len() as u8);
        d
    };

    let msg_prime = {
        let mut m = Vec::with_capacity(64 + input.len() + 2 + 1 + dst_prime.len());
        m.extend_from_slice(&[0u8; 64]);
        m.extend_from_slice(input);
        m.extend_from_slice(&(len_in_bytes as u16).to_be_bytes());
        m.push(0u8);
        m.extend_from_slice(&dst_prime);
        m
    };

    let b_0 = {
        let mut hasher = Sha256::new();
        hasher.update(&msg_prime);
        hasher.finalize()
    };

    let mut b_vals = Vec::with_capacity(ell);
    let b_1 = {
        let mut hasher = Sha256::new();
        hasher.update(b_0.as_slice());
        hasher.update([0x01]);
        hasher.update(&dst_prime);
        hasher.finalize()
    };
    b_vals.push(b_1);

    for i in 2..=ell {
        let prev = &b_vals[i - 2];
        let mut xored = [0u8; HASH_LEN];
        for j in 0..HASH_LEN {
            xored[j] = b_0[j] ^ prev[j];
        }

        let mut hasher = Sha256::new();
        hasher.update(xored);
        hasher.update([i as u8]);
        hasher.update(&dst_prime);
        b_vals.push(hasher.finalize());
    }

    let mut result = Vec::with_capacity(len_in_bytes);
    for b in b_vals {
        result.extend_from_slice(&b);
        if result.len() >= len_in_bytes {
            break;
        }
    }
    result.truncate(len_in_bytes);
    result
}
