#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;

use crate::big_int::u1024::U1024;
use crate::traits::BigInt;

#[target_feature(enable = "avx2")]
pub unsafe fn xor(a: &U1024, b: &U1024) -> U1024 {
    unsafe {
        let mut res = U1024::zero();

        let a_ptr = a.0.as_ptr() as *const __m256i;
        let b_ptr = b.0.as_ptr() as *const __m256i;
        let res_ptr = res.0.as_mut_ptr() as *mut __m256i;

        for i in 0..4 {
            let va = _mm256_loadu_si256(a_ptr.add(i));
            let vb = _mm256_loadu_si256(b_ptr.add(i));
            let vr = _mm256_xor_si256(va, vb);
            _mm256_storeu_si256(res_ptr.add(i), vr);
        }

        res
    }
}

#[target_feature(enable = "avx2")]
pub unsafe fn conditional_select(a: &U1024, b: &U1024, choice: bool) -> U1024 {
    unsafe {
        let mut res = U1024::zero();

        let mask_val = if choice { -1i64 } else { 0 };
        let mask_vec = _mm256_set1_epi64x(mask_val);

        let a_ptr = a.0.as_ptr() as *const __m256i;
        let b_ptr = b.0.as_ptr() as *const __m256i;
        let res_ptr = res.0.as_mut_ptr() as *mut __m256i;

        for i in 0..4 {
            let va = _mm256_loadu_si256(a_ptr.add(i));
            let vb = _mm256_loadu_si256(b_ptr.add(i));

            let vr = _mm256_blendv_epi8(vb, va, mask_vec);

            _mm256_storeu_si256(res_ptr.add(i), vr);
        }

        res
    }
}
