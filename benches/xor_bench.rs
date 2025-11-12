use std::hint::black_box;

use criterion::{Criterion, criterion_group, criterion_main};

use mathlib::core::int::BigInt;
use mathlib::num::int::u256::U256;

fn xor_benchmark(c: &mut Criterion) {
    let a = U256([1, 2, 3, 4, 5, 6, 7, 8]);
    let b = U256([5, 6, 7, 8, 1, 2, 3, 4]);

    let mut group = c.benchmark_group("U256 XOR Comparison");

    fn xor_safe_fallback(a: &U256, b: &U256) -> U256 {
        let mut result = U256::ZERO;
        for i in 0..8 {
            result.0[i] = a.0[i] ^ b.0[i];
        }
        result
    }

    group.bench_function("XOR (Safe Fallback)", |ben| {
        ben.iter(|| xor_safe_fallback(black_box(&a), black_box(&b)))
    });

    group.bench_function("XOR (AVX2 Dispatch)", |ben| {
        ben.iter(|| black_box(a) ^ black_box(b))
    });

    group.finish();
}

criterion_group!(benches, xor_benchmark);
criterion_main!(benches);
