use crate::U1024;
use crate::traits::BigInt;

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
pub struct MontgomeryParams {
    pub modulus: U1024,
    pub r2: U1024,
    pub n_prime: U1024,
    pub root_of_unity: U1024,
}

impl MontgomeryParams {
    /// Constructs MontgomeryParams for the given field modulus and root of unity.
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
    /// use mathlib::U1024;
    /// use mathlib::field::montgomery::MontgomeryParams;
    /// use mathlib::traits::BigInt;
    ///
    /// // Construct parameters for modulus 17 with root of unity 3
    /// let m = U1024::from_u64(17);
    /// let w = U1024::from_u64(3);
    /// let params = MontgomeryParams::new(m.clone(), w);
    /// assert_eq!(params.modulus, m);
    /// assert_eq!(params.root_of_unity, w);
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
    /// use mathlib::U1024;
    /// use mathlib::field::montgomery::MontgomeryParams;
    /// use mathlib::traits::BigInt;
    ///
    /// let m = U1024::from_u64(3);
    /// let n_prime = MontgomeryParams::compute_n_prime(&m);
    /// let _ = n_prime; // n_prime can now be used in Montgomery reduction
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
    /// use mathlib::U1024;
    /// use mathlib::field::montgomery::MontgomeryParams;
    /// use mathlib::traits::BigInt;
    ///
    /// let m = U1024::from_u64(3);
    /// let r2 = MontgomeryParams::compute_r2(&m);
    /// // 2^2048 mod 3 == 1
    /// assert_eq!(r2, U1024::one());
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
    /// use mathlib::U1024;
    /// use mathlib::field::montgomery::MontgomeryParams;
    /// use mathlib::traits::BigInt;
    ///
    /// let params = MontgomeryParams {
    ///     modulus: U1024::one(),
    ///     r2: U1024::one(),
    ///     n_prime: U1024::one(),
    ///     root_of_unity: U1024::one(),
    /// };
    /// let lo = U1024::zero();
    /// let hi = U1024::zero();
    /// assert_eq!(params.reduce(&lo, &hi), U1024::zero());
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
