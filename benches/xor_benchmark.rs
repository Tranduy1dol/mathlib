use std::hint::black_box;

use criterion::{criterion_group, criterion_main, Criterion};

use mathlib::num::u256::U256;

fn xor_benchmark(c: &mut Criterion) {
    let a = U256([1, 2, 3, 4]);
    let b = U256([5, 6, 7, 8]);

    let mut group = c.benchmark_group("XOR Comparison");

    group.bench_function("XOR (Safe, by-ref)", |ben| {
        ben.iter(|| black_box(a).xor_safe(black_box(&b)))
    });

    group.bench_function("XOR (Trait Dispatcher, by-val)", |ben| {
        ben.iter(|| black_box(a) ^ black_box(b))
    });

    if is_x86_feature_detected!("avx2") {
        group.bench_function("XOR (AVX2 Direct, by-ref)", |ben| {
            ben.iter(|| unsafe {
                mathlib::arch::x86_64::avx2::xor_avx2(black_box(&a), black_box(&b))
            })
        });
    }

    group.finish();
}

criterion_group!(benches, xor_benchmark);
criterion_main!(benches);