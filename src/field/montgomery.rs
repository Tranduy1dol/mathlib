use crate::{BigInt, U1024};

/// Macro to create MontgomeryContext from different sources.
///
/// # Examples
///
/// ```
/// use lumen_math::{mont, u1024};
///
/// // From U1024 values
/// let params = mont!(u1024!(17), u1024!(2));
///
/// // From primitive types
/// let params2 = mont!(17u64, 2u64);
/// let params3 = mont!(17u32, 2u32);
///
/// // From hex strings
/// let params4 = mont!("0x11", "0x2");
/// ```
#[macro_export]
macro_rules! mont {
    // Two arguments: modulus and root_of_unity
    ($modulus:expr, $root:expr) => {{
        #[allow(unused_imports)]
        {
            // Helper trait to convert to U1024
            trait ToU1024Param {
                fn to_u1024_param(self) -> $crate::U1024;
            }

            impl ToU1024Param for &str {
                fn to_u1024_param(self) -> $crate::U1024 {
                    $crate::U1024::from_hex(self)
                }
            }

            impl ToU1024Param for u8 {
                fn to_u1024_param(self) -> $crate::U1024 {
                    $crate::U1024::from_u8(self)
                }
            }

            impl ToU1024Param for u16 {
                fn to_u1024_param(self) -> $crate::U1024 {
                    $crate::U1024::from_u16(self)
                }
            }

            impl ToU1024Param for u32 {
                fn to_u1024_param(self) -> $crate::U1024 {
                    $crate::U1024::from_u32(self)
                }
            }

            impl ToU1024Param for u64 {
                fn to_u1024_param(self) -> $crate::U1024 {
                    $crate::U1024::from_u64(self)
                }
            }

            impl ToU1024Param for u128 {
                fn to_u1024_param(self) -> $crate::U1024 {
                    $crate::U1024::from_u128(self)
                }
            }

            impl ToU1024Param for $crate::U1024 {
                fn to_u1024_param(self) -> $crate::U1024 {
                    self
                }
            }

            $crate::field::montgomery::MontgomeryContext::new(
                ToU1024Param::to_u1024_param($modulus),
                ToU1024Param::to_u1024_param($root),
            )
        }
    }};
}

/// Montgomery parameters for efficient modular arithmetic in a prime field.
///
/// This struct holds precomputed values needed for Montgomery reduction,
/// which enables fast modular multiplication without expensive division operations.
///
/// # Fields
///
/// - `modulus`: The prime field modulus P
/// - `r2`: R^2 mod P, where R = 2^1024, used for converting to Montgomery form
/// - `n_prime`: Montgomery constant satisfying P * n' ≡ -1 (mod 2^1024)
/// - `root_of_unity`: A primitive root of unity in the field, used for NTT operations
#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub struct MontgomeryContext {
    pub modulus: U1024,
    pub r2: U1024,
    pub n_prime: U1024,
    pub root_of_unity: U1024,
}

impl MontgomeryContext {
    /// Constructs MontgomeryContext for the given field modulus and root of unity.
    ///
    /// This function precomputes the Montgomery constant n' and the value R^2 mod modulus
    /// needed for efficient Montgomery arithmetic. The root of unity is stored for use in
    /// Number Theoretic Transform (NTT) operations.
    ///
    /// # Arguments
    ///
    /// * `modulus` - The prime field modulus P
    /// * `root_of_unity` - A primitive root of unity in the field (typically W where W^n = 1 mod P)
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::{mont, u1024};
    ///
    /// // Construct parameters for modulus 17 with root of unity 3
    /// let m = u1024!(17);
    /// let w = u1024!(3);
    /// let params = mont!(m, w);
    /// assert_eq!(params.modulus, u1024!(17));
    /// assert_eq!(params.root_of_unity, u1024!(3));
    /// ```
    pub fn new(modulus: U1024, root_of_unity: U1024) -> Self {
        let n_prime = Self::compute_n_prime(&modulus);
        let r2 = Self::compute_r2(&modulus);

        Self {
            modulus,
            r2,
            n_prime,
            root_of_unity,
        }
    }

    /// Computes the Montgomery n' value for a modulus: the value `n_prime` satisfying
    /// `modulus * n_prime ≡ -1 (mod 2^1024)`.
    ///
    /// The modulus must be odd for inverse modulo 2^k to exist; behavior for even
    /// modulus is undefined.
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::{u1024, U1024};
    /// use lumen_math::field::montgomery::MontgomeryContext;
    ///
    /// let m = u1024!(3u64);
    /// let n_prime = MontgomeryContext::compute_n_prime(&m);
    /// let _: U1024 = n_prime; // n_prime can now be used in Montgomery reduction
    /// ```
    pub fn compute_n_prime(modulus: &U1024) -> U1024 {
        let mut inv = 1u64;
        let p0 = modulus.0[0];

        for _ in 0..6 {
            inv = inv.wrapping_mul(2u64.wrapping_sub(p0.wrapping_mul(inv)));
        }

        let mut inv_big = U1024::from_u64(inv);

        let two = U1024::from_u64(2);

        for _ in 0..4 {
            let term = *modulus * inv_big;

            let (correction, _) = two.borrowing_sub(&term);

            inv_big = inv_big * correction;
        }

        let (neg_inv, _) = U1024::zero().borrowing_sub(&inv_big);
        neg_inv
    }

    /// Computes R^2 modulo `modulus`, where R = 2^1024.
    ///
    /// The returned value equals 2^2048 mod `moduli`, represented as a `U1024`.
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::{u1024, BigInt};
    /// use lumen_math::field::montgomery::MontgomeryContext;
    ///
    /// let m = u1024!(3u64);
    /// let r2 = MontgomeryContext::compute_r2(&m);
    /// // 2^2048 mod 3 == 1
    /// assert_eq!(r2, u1024!(1u64));
    /// ```
    pub fn compute_r2(modulus: &U1024) -> U1024 {
        let mut acc = U1024::one();

        for _ in 0..2048 {
            let (acc_shifted, carry) = acc.carrying_add(&acc);
            let (sub_res, borrow) = acc_shifted.borrowing_sub(modulus);

            if carry || !borrow {
                acc = sub_res;
            } else {
                acc = acc_shifted;
            }
        }

        acc
    }

    /// Reduces a 2048-bit value represented by (`hi`, `lo`) to a canonical 1024-bit residue modulo `self.modulus` using Montgomery reduction.
    ///
    /// `lo` is the low 1024 bits and `hi` is the high 1024 bits of the 2048-bit integer to reduce. The method uses `self.n_prime` and `self.modulus` to compute the Montgomery reduction and returns the resulting value in the range [0, modulus).
    ///
    /// # Examples
    ///
    /// ```
    /// use lumen_math::u1024;
    /// use lumen_math::field::montgomery::MontgomeryContext;
    ///
    /// let params = MontgomeryContext {
    ///     modulus: u1024!(1u64),
    ///     r2: u1024!(1u64),
    ///     n_prime: u1024!(1u64),
    ///     root_of_unity: u1024!(1u64),
    /// };
    /// let lo = u1024!(0u64);
    /// let hi = u1024!(0u64);
    /// assert_eq!(params.reduce(&lo, &hi), u1024!(0u64));
    /// ```
    #[inline]
    pub fn reduce(&self, lo: &U1024, hi: &U1024) -> U1024 {
        let m = (*lo) * self.n_prime;
        let (mn_lo, mn_hi) = m.full_mul(&self.modulus);

        let (_, carry_lo) = lo.carrying_add(&mn_lo);
        let (res_hi, carry_hi) = hi.carrying_add(&mn_hi);
        let (t, carry_final) = if carry_lo {
            res_hi.carrying_add(&U1024::one())
        } else {
            (res_hi, false)
        };

        if carry_hi || carry_final {
            let (sub_res, _) = t.borrowing_sub(&self.modulus);
            return sub_res;
        }

        let (sub_res, borrow) = t.borrowing_sub(&self.modulus);
        if !borrow { sub_res } else { t }
    }
}
