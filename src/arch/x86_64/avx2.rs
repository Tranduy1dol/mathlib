use std::arch::x86_64::*;

use crate::core::int::BigInt;
use crate::num::int::u256::U256;

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn u256_xor_avx2(a: &U256, b: &U256) -> U256 {
    unsafe {
        use core::arch::x86_64::*;

        let a_vec = _mm256_loadu_si256(a.0.as_ptr() as *const __m256i);
        let b_vec = _mm256_loadu_si256(b.0.as_ptr() as *const __m256i);

        let result_vec = _mm256_xor_si256(a_vec, b_vec);

        let mut result = U256::ZERO;
        _mm256_storeu_si256(result.0.as_mut_ptr() as *mut __m256i, result_vec);

        result
    }
}

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
