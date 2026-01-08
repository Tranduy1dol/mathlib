//! Constant-time benchmarks for timing analysis
//!
//! These benchmarks compare execution times with different Hamming weights (number of set bits)
//! to verify that the implementations are constant-time.
//!
//! For a truly constant-time implementation:
//! - Low Hamming weight inputs should take the same time as high Hamming weight inputs
//! - The timing difference should be within noise margins (~5%)
//!
//! Run with: cargo bench --bench constant_time_bench

use std::hint::black_box;

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};

use lumen_math::U1024;
use lumen_math::traits::BigInt;

// ============================================================================
// conditional_select Benchmarks
// ============================================================================

fn bench_conditional_select(c: &mut Criterion) {
    let a = U1024([0xAAAA_AAAA_AAAA_AAAA; 16]);
    let b = U1024([0x5555_5555_5555_5555; 16]);

    let mut group = c.benchmark_group("conditional_select");

    group.bench_function("choice_true", |bencher| {
        bencher.iter(|| U1024::conditional_select(black_box(&a), black_box(&b), black_box(true)))
    });

    group.bench_function("choice_false", |bencher| {
        bencher.iter(|| U1024::conditional_select(black_box(&a), black_box(&b), black_box(false)))
    });

    // Alternating choice to prevent branch prediction
    group.bench_function("alternating", |bencher| {
        let mut choice = false;
        bencher.iter(|| {
            choice = !choice;
            U1024::conditional_select(black_box(&a), black_box(&b), black_box(choice))
        })
    });

    group.finish();
}

// ============================================================================
// bits() Benchmarks
// ============================================================================

fn bench_bits(c: &mut Criterion) {
    // Different bit patterns to test constant-time behavior
    let zero = U1024::ZERO;
    let small = U1024::from_u64(1); // Only 1 bit used
    let medium = U1024::from_u64(u64::MAX); // 64 bits used
    let large = U1024([u64::MAX; 16]); // All 1024 bits used

    // Sparse pattern (only high bit set in highest limb)
    let mut sparse = U1024::ZERO;
    sparse.0[15] = 1u64 << 63;

    let mut group = c.benchmark_group("bits");

    group.bench_function("zero", |bencher| bencher.iter(|| black_box(&zero).bits()));

    group.bench_function("small_1bit", |bencher| {
        bencher.iter(|| black_box(&small).bits())
    });

    group.bench_function("medium_64bits", |bencher| {
        bencher.iter(|| black_box(&medium).bits())
    });

    group.bench_function("large_1024bits", |bencher| {
        bencher.iter(|| black_box(&large).bits())
    });

    group.bench_function("sparse_high_limb", |bencher| {
        bencher.iter(|| black_box(&sparse).bits())
    });

    group.finish();
}

// ============================================================================
// mod_pow Benchmarks - Critical for Constant-Time Analysis
// ============================================================================

fn bench_mod_pow_hamming_weight(c: &mut Criterion) {
    let base = U1024::from_u64(17);
    let modulus = U1024::from_hex(
        "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFB43",
    );

    // Different Hamming weights for the exponent
    // Low HW: only 1 bit set
    let exp_hw_1 = U1024::from_u64(0x8000_0000_0000_0000);

    // Medium HW: ~32 bits set (alternating pattern in one limb)
    let exp_hw_32 = U1024::from_u64(0xAAAA_AAAA_AAAA_AAAA);

    // High HW: 64 bits set (all ones in one limb)
    let exp_hw_64 = U1024::from_u64(u64::MAX);

    // Very high HW: multiple limbs with bits
    let mut exp_hw_128 = U1024::ZERO;
    exp_hw_128.0[0] = u64::MAX;
    exp_hw_128.0[1] = u64::MAX;

    let mut group = c.benchmark_group("mod_pow_hamming_weight");

    // Use fewer samples for expensive operations
    group.sample_size(50);

    group.bench_with_input(
        BenchmarkId::new("hamming_weight", "1"),
        &exp_hw_1,
        |b, exp| b.iter(|| black_box(&base).mod_pow(black_box(exp), black_box(&modulus))),
    );

    group.bench_with_input(
        BenchmarkId::new("hamming_weight", "32"),
        &exp_hw_32,
        |b, exp| b.iter(|| black_box(&base).mod_pow(black_box(exp), black_box(&modulus))),
    );

    group.bench_with_input(
        BenchmarkId::new("hamming_weight", "64"),
        &exp_hw_64,
        |b, exp| b.iter(|| black_box(&base).mod_pow(black_box(exp), black_box(&modulus))),
    );

    group.bench_with_input(
        BenchmarkId::new("hamming_weight", "128"),
        &exp_hw_128,
        |b, exp| b.iter(|| black_box(&base).mod_pow(black_box(exp), black_box(&modulus))),
    );

    group.finish();
}

// ============================================================================
// div_rem Benchmarks
// ============================================================================

fn bench_div_rem(c: &mut Criterion) {
    let divisor = U1024::from_u64(1_000_000_007);

    // Different dividend sizes
    let small_dividend = U1024::from_u64(123456789);
    let medium_dividend = U1024::from_u64(u64::MAX);

    // Large dividend using multiple limbs
    let mut large_dividend = U1024::ZERO;
    large_dividend.0[0] = u64::MAX;
    large_dividend.0[1] = u64::MAX;
    large_dividend.0[2] = 0x1234;

    let mut group = c.benchmark_group("div_rem");

    group.sample_size(50);

    group.bench_function("small_dividend", |bencher| {
        bencher.iter(|| black_box(&small_dividend).div_rem(black_box(&divisor)))
    });

    group.bench_function("medium_dividend", |bencher| {
        bencher.iter(|| black_box(&medium_dividend).div_rem(black_box(&divisor)))
    });

    group.bench_function("large_dividend", |bencher| {
        bencher.iter(|| black_box(&large_dividend).div_rem(black_box(&divisor)))
    });

    group.finish();
}

// ============================================================================
// Comparative Timing Analysis
//
// This benchmark is specifically designed to detect timing leaks.
// It runs the same operation many times with different secret values
// and compares the timing distributions.
// ============================================================================

fn bench_timing_leak_detection(c: &mut Criterion) {
    let base = U1024::from_u64(7);
    let modulus = U1024::from_u64(1_000_000_007);

    // Create exponents with extreme Hamming weight differences
    // If implementation is constant-time, these should take identical time

    // Exponent with minimal bits set (sparse)
    let exp_sparse = U1024::from_u64(1); // Just 1 bit

    // Exponent with maximum bits set (dense)
    let exp_dense = U1024::from_u64(u64::MAX); // 64 bits

    let mut group = c.benchmark_group("timing_leak_detection");

    group.sample_size(100);

    group.bench_function("mod_pow_sparse_exp", |bencher| {
        bencher.iter(|| black_box(&base).mod_pow(black_box(&exp_sparse), black_box(&modulus)))
    });

    group.bench_function("mod_pow_dense_exp", |bencher| {
        bencher.iter(|| black_box(&base).mod_pow(black_box(&exp_dense), black_box(&modulus)))
    });

    // conditional_select timing comparison
    let a = U1024([0x1234_5678_9ABC_DEF0; 16]);
    let b = U1024([0xFEDC_BA98_7654_3210; 16]);

    group.bench_function("ct_select_true", |bencher| {
        bencher.iter(|| U1024::conditional_select(black_box(&a), black_box(&b), black_box(true)))
    });

    group.bench_function("ct_select_false", |bencher| {
        bencher.iter(|| U1024::conditional_select(black_box(&a), black_box(&b), black_box(false)))
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_conditional_select,
    bench_bits,
    bench_mod_pow_hamming_weight,
    bench_div_rem,
    bench_timing_leak_detection,
);
criterion_main!(benches);
