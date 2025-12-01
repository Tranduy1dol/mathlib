#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;

use crate::big_int::u1024::U1024;
use crate::traits::BigInt;

/// Computes the bitwise XOR of two U1024 values using AVX2 SIMD instructions.
///
/// This function processes the 1024-bit values in four 256-bit chunks using AVX2
/// vector operations for improved performance.
///
/// # Safety
///
/// This function is unsafe because:
/// - It requires AVX2 CPU support. The caller must ensure the target CPU supports AVX2.
/// - It uses raw pointer arithmetic and assumes `U1024` has a specific memory layout
///   (16 contiguous u64 limbs, 128 bytes total).
/// - The function is marked with `#[target_feature(enable = "avx2")]`, so it must only
///   be called on systems where AVX2 is available, or from code that has verified AVX2
///   support at runtime.
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

/// Performs a constant-time conditional selection between two U1024 values using AVX2.
///
/// Returns `a` if `choice` is `true`, otherwise returns `b`. The selection is performed
/// using SIMD blend operations to avoid branching and maintain constant-time behavior.
///
/// # Safety
///
/// This function is unsafe because:
/// - It requires AVX2 CPU support. The caller must ensure the target CPU supports AVX2.
/// - It uses raw pointer arithmetic and assumes `U1024` has a specific memory layout
///   (16 contiguous u64 limbs, 128 bytes total).
/// - The function is marked with `#[target_feature(enable = "avx2")]`, so it must only
///   be called on systems where AVX2 is available, or from code that has verified AVX2
///   support at runtime.
#[target_feature(enable = "avx2")]
pub unsafe fn conditional_select(a: &U1024, b: &U1024, choice: bool) -> U1024 {
    unsafe {
        let mut res = U1024::zero();

        let mask_val = -(choice as i64);
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
