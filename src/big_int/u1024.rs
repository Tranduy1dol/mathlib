use std::cmp::Ordering;
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

/// Macro to create a U1024 value from different sources.
///
/// # Examples
///
/// ```
/// use mathlib::u1024;
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
    /// use mathlib::u1024;
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
    /// use mathlib::u1024;
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
        for (i, limb) in self.0.iter().enumerate().rev() {
            if *limb != 0 {
                return (i + 1) * 64 - limb.leading_zeros() as usize;
            }
        }
        0
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
    /// use mathlib::u1024;
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
    /// use mathlib::u1024;
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
    /// use mathlib::u1024;
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
    /// use mathlib::u1024;
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
    /// use mathlib::u1024;
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
    /// use mathlib::u1024;
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
    /// use mathlib::U1024;
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
    /// use mathlib::U1024;
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
    /// use mathlib::U1024;
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

impl PartialOrd for U1024 {
    /// Compares two U1024 values.
    ///
    /// Comparison is performed from the most-significant limb to the least-significant
    /// limb, returning as soon as a difference is found.
    ///
    /// # Examples
    ///
    /// ```
    /// use mathlib::u1024;
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
    /// use mathlib::u1024;
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
