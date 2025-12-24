//! Chinese Remainder Theorem (CRT) solver implementation for U1024.
//!
//! The Chinese Remainder Theorem states that if we have a system of congruences:
//!   x ≡ a₁ (mod n₁)
//!   x ≡ a₂ (mod n₂)
//!   ...
//!   x ≡ aₖ (mod nₖ)
//!
//! where n₁, n₂, ..., nₖ are pairwise coprime, then there exists a unique solution
//! x modulo N = n₁ × n₂ × ... × nₖ.

use super::gcd::mod_inverse;
use crate::U1024;
use crate::traits::BigInt;

/// Error type for Chinese Remainder Theorem operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CrtError {
    /// No congruences provided.
    EmptyInput,
    /// Moduli are not pairwise coprime.
    ModuliNotCoprime,
    /// Mismatched lengths of remainders and moduli.
    LengthMismatch,
    /// Product of moduli overflows U1024.
    ProductOverflow,
}

impl std::fmt::Display for CrtError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CrtError::EmptyInput => write!(f, "No congruences provided"),
            CrtError::ModuliNotCoprime => write!(f, "Moduli must be pairwise coprime"),
            CrtError::LengthMismatch => write!(f, "Remainders and moduli must have same length"),
            CrtError::ProductOverflow => write!(f, "Product of moduli overflows 1024 bits"),
        }
    }
}

impl std::error::Error for CrtError {}

/// Solves a system of linear congruences using the Chinese Remainder Theorem.
///
/// Given pairs (aᵢ, nᵢ), finds x such that x ≡ aᵢ (mod nᵢ) for all i.
///
/// # Arguments
///
/// * `remainders` - The remainders a₁, a₂, ..., aₖ
/// * `moduli` - The moduli n₁, n₂, ..., nₖ (must be pairwise coprime)
///
/// # Returns
///
/// * `Ok(x)` - The unique solution modulo the product of all moduli
/// * `Err(CrtError)` - If the input is invalid or moduli are not coprime
///
/// # Examples
///
/// ```
/// use mathlib::protocol::chinese_remainder_solver;
/// use mathlib::U1024;
///
/// // x ≡ 2 (mod 3)
/// // x ≡ 3 (mod 5)
/// // x ≡ 2 (mod 7)
/// // Solution: x = 23 (mod 105)
/// let remainders = vec![
///     U1024::from_u64(2),
///     U1024::from_u64(3),
///     U1024::from_u64(2),
/// ];
/// let moduli = vec![
///     U1024::from_u64(3),
///     U1024::from_u64(5),
///     U1024::from_u64(7),
/// ];
/// let result = chinese_remainder_solver(&remainders, &moduli).unwrap();
/// assert_eq!(result, U1024::from_u64(23));
/// ```
pub fn chinese_remainder_solver(remainders: &[U1024], moduli: &[U1024]) -> Result<U1024, CrtError> {
    if remainders.is_empty() || moduli.is_empty() {
        return Err(CrtError::EmptyInput);
    }

    if remainders.len() != moduli.len() {
        return Err(CrtError::LengthMismatch);
    }

    // Compute the product of all moduli
    let mut n = U1024::from_u64(1);
    for m in moduli {
        let (prod_lo, prod_hi) = n.const_mul(m);
        if prod_hi != U1024::ZERO {
            return Err(CrtError::ProductOverflow);
        }
        n = prod_lo;
    }

    let mut result = U1024::ZERO;

    for (a_i, n_i) in remainders.iter().zip(moduli.iter()) {
        // N_i = N / n_i
        let big_n_i = n / *n_i;

        // y_i = N_i^(-1) mod n_i
        let y_i = mod_inverse(big_n_i, *n_i).ok_or(CrtError::ModuliNotCoprime)?;

        // Compute a_i * N_i * y_i mod n
        // We use mod_mul to safely handle products up to 2048 bits.
        // term = (a_i * N_i * y_i) mod n
        let tmp = a_i.mod_mul(&big_n_i, &n);
        let term = tmp.mod_mul(&y_i, &n);

        // Add to result mod n using safe modular addition
        // Both result and term are < n, so their true sum is < 2n
        // We need to compute (result + term) % n safely, handling potential overflow
        let (sum, carry) = result.carrying_add(&term);
        if carry {
            // sum wrapped around 2^1024, true_sum = sum + 2^1024
            // Since result < n and term < n, true_sum < 2n
            // And true_sum >= 2^1024 >= n, so true_sum - n is the correct result
            // true_sum - n = sum + 2^1024 - n = sum + (2^1024 - n)
            // (2^1024 - n) in wrapping arithmetic is (U1024::ZERO - n)
            // This addition is safe: sum < 2n - 2^1024, and when n > 2^1023,
            // sum < 2n - 2^1024 < n, so sum + (2^1024 - n) < 2^1024 (no overflow)
            result = sum + (U1024::ZERO - n);
        } else if sum >= n {
            // No overflow, but sum >= n, so subtract n
            result = sum - n;
        } else {
            result = sum;
        }
    }

    Ok(result)
}

/// Simpler wrapper for solving two congruences.
///
/// Solves the system:
///   x ≡ a₁ (mod n₁)
///   x ≡ a₂ (mod n₂)
///
/// # Arguments
///
/// * `a1` - First remainder
/// * `n1` - First modulus
/// * `a2` - Second remainder
/// * `n2` - Second modulus
///
/// # Returns
///
/// * `Ok(x)` - The unique solution modulo n₁ × n₂
/// * `Err(CrtError)` - If moduli are not coprime
///
/// # Examples
///
/// ```
/// use mathlib::protocol::chinese_remainder;
/// use mathlib::U1024;
///
/// // x ≡ 2 (mod 3) and x ≡ 3 (mod 5)
/// // Solution: x = 8 (mod 15)
/// let result = chinese_remainder(
///     U1024::from_u64(2), U1024::from_u64(3),
///     U1024::from_u64(3), U1024::from_u64(5)
/// ).unwrap();
/// assert_eq!(result, U1024::from_u64(8));
/// ```
pub fn chinese_remainder(a1: U1024, n1: U1024, a2: U1024, n2: U1024) -> Result<U1024, CrtError> {
    chinese_remainder_solver(&[a1, a2], &[n1, n2])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_crt_basic() {
        // x ≡ 2 (mod 3)
        // x ≡ 3 (mod 5)
        // x ≡ 2 (mod 7)
        // Solution: x = 23 (mod 105)
        let remainders = vec![U1024::from_u64(2), U1024::from_u64(3), U1024::from_u64(2)];
        let moduli = vec![U1024::from_u64(3), U1024::from_u64(5), U1024::from_u64(7)];
        let result = chinese_remainder_solver(&remainders, &moduli).unwrap();
        assert_eq!(result, U1024::from_u64(23));

        // Verify
        assert_eq!(U1024::from_u64(23) % U1024::from_u64(3), U1024::from_u64(2));
        assert_eq!(U1024::from_u64(23) % U1024::from_u64(5), U1024::from_u64(3));
        assert_eq!(U1024::from_u64(23) % U1024::from_u64(7), U1024::from_u64(2));
    }

    #[test]
    fn test_crt_two_congruences() {
        // x ≡ 2 (mod 3) and x ≡ 3 (mod 5)
        let result = chinese_remainder(
            U1024::from_u64(2),
            U1024::from_u64(3),
            U1024::from_u64(3),
            U1024::from_u64(5),
        )
        .unwrap();
        assert_eq!(result, U1024::from_u64(8));

        assert_eq!(U1024::from_u64(8) % U1024::from_u64(3), U1024::from_u64(2));
        assert_eq!(U1024::from_u64(8) % U1024::from_u64(5), U1024::from_u64(3));
    }

    #[test]
    fn test_crt_empty_input() {
        let result = chinese_remainder_solver(&[], &[]);
        assert_eq!(result, Err(CrtError::EmptyInput));
    }

    #[test]
    fn test_crt_length_mismatch() {
        let result = chinese_remainder_solver(
            &[U1024::from_u64(1), U1024::from_u64(2)],
            &[U1024::from_u64(3)],
        );
        assert_eq!(result, Err(CrtError::LengthMismatch));
    }

    #[test]
    fn test_crt_not_coprime() {
        // 4 and 6 are not coprime (gcd = 2)
        let result = chinese_remainder_solver(
            &[U1024::from_u64(1), U1024::from_u64(2)],
            &[U1024::from_u64(4), U1024::from_u64(6)],
        );
        assert_eq!(result, Err(CrtError::ModuliNotCoprime));
    }

    #[test]
    fn test_crt_single_congruence() {
        let result =
            chinese_remainder_solver(&[U1024::from_u64(5)], &[U1024::from_u64(7)]).unwrap();
        assert_eq!(result, U1024::from_u64(5));
    }

    #[test]
    fn test_crt_larger_numbers() {
        // x ≡ 0 (mod 3)
        // x ≡ 3 (mod 4)
        // x ≡ 4 (mod 5)
        // Solution: x = 39 (mod 60)
        let remainders = vec![U1024::from_u64(0), U1024::from_u64(3), U1024::from_u64(4)];
        let moduli = vec![U1024::from_u64(3), U1024::from_u64(4), U1024::from_u64(5)];
        let result = chinese_remainder_solver(&remainders, &moduli).unwrap();
        assert_eq!(result, U1024::from_u64(39));

        assert_eq!(U1024::from_u64(39) % U1024::from_u64(3), U1024::ZERO);
        assert_eq!(U1024::from_u64(39) % U1024::from_u64(4), U1024::from_u64(3));
        assert_eq!(U1024::from_u64(39) % U1024::from_u64(5), U1024::from_u64(4));
    }
}
