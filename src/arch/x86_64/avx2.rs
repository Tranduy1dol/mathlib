use std::arch::x86_64::*;

use crate::core::int::BigInt;
use crate::num::int::u256::U256;

/// Compute the bitwise XOR of two 256-bit values using AVX2.
///
/// Returns a `U256` containing the bitwise XOR of `a` and `b`.
///
/// # Examples
///
/// ```
/// let a = U256([1u64, 0, 0, 0, 0, 0, 0, 0]);
/// let b = U256([2u64, 0, 0, 0, 0, 0, 0, 0]);
/// let c = unsafe { xor_avx2(&a, &b) };
/// assert_eq!(c, U256([3u64, 0, 0, 0, 0, 0, 0, 0]));
/// ```
#[target_feature(enable = "avx2")]
pub unsafe fn xor_avx2(a: &U256, b: &U256) -> U256 {
    unsafe {
        let a_ptr = a.0.as_ptr() as *const __m256i;
        let b_ptr = b.0.as_ptr() as *const __m256i;

        let a_vec = _mm256_load_si256(a_ptr);
        let b_vec = _mm256_load_si256(b_ptr);

        let result_vec = _mm256_xor_si256(a_vec, b_vec);

        let mut result = U256([0; 8]);
        let res_ptr = result.0.as_mut_ptr() as *mut __m256i;

        _mm256_store_si256(res_ptr, result_vec);

        result
    }
}

/// Selects bits from `a` or `b` according to `mask`, returning the assembled `U256`.
///
/// For each bit position, the returned `U256` contains the bit from `a` when the
/// corresponding bit in `mask` is set, and the bit from `b` otherwise.
///
/// # Parameters
///
/// - `a`: Source `U256` supplying bits where `mask` is set.
/// - `b`: Source `U256` supplying bits where `mask` is clear.
/// - `mask`: Selection mask; bits set choose from `a`, bits clear choose from `b`.
///
/// # Returns
///
/// The `U256` composed from bits of `a` and `b` according to `mask`.
///
/// # Examples
///
/// ```
/// let a = U256::ZERO;
/// let b = U256::ZERO;
/// let mask = U256::ZERO;
/// let res = unsafe { u256_conditional_select_avx2(&a, &b, &mask) };
/// assert_eq!(res, b);
/// ```
#[target_feature(enable = "avx2")]
pub unsafe fn u256_conditional_select_avx2(a: &U256, b: &U256, mask: &U256) -> U256 {
    unsafe {
        let a_ptr = a.0.as_ptr() as *const __m256i;
        let b_ptr = b.0.as_ptr() as *const __m256i;
        let mask_ptr = mask.0.as_ptr() as *const __m256i;

        let a_vec = _mm256_load_si256(a_ptr);
        let b_vec = _mm256_load_si256(b_ptr);
        let mask_vec = _mm256_load_si256(mask_ptr);

        let result_vec = _mm256_blendv_epi8(b_vec, a_vec, mask_vec);

        let mut result = U256::ZERO;
        let res_ptr = result.0.as_mut_ptr() as *mut __m256i;
        _mm256_store_si256(res_ptr, result_vec);

        result
    }
}