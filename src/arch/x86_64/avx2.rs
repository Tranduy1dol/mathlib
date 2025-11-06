use std::arch::x86_64::*;

use crate::num::u256::U256;

#[target_feature(enable = "avx2")]
pub unsafe fn xor_avx2(a: &U256, b: &U256) -> U256 {
    unsafe {
        let a_ptr = a.0.as_ptr() as *const __m256i;
        let b_ptr = b.0.as_ptr() as *const __m256i;

        let a_vec = _mm256_load_si256(a_ptr);
        let b_vec = _mm256_load_si256(b_ptr);

        let result_vec = _mm256_xor_si256(a_vec, b_vec);

        let mut result = U256([0; 4]);
        let res_ptr = result.0.as_mut_ptr() as *mut __m256i;

        _mm256_store_si256(res_ptr, result_vec);

        result
    }
}
