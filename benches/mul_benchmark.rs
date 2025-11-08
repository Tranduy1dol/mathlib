use std::hint::black_box;

use criterion::{Criterion, criterion_group, criterion_main};

use mathlib::num::u256::U256;

fn mul_benchmark(c: &mut Criterion) {
    let a = U256([
        0u64.wrapping_sub(1),
        0u64.wrapping_sub(2),
        0u64.wrapping_sub(3),
        0u64.wrapping_sub(4),
    ]);
    let b = U256([5, 6, 7, 8]);

    let mut group = c.benchmark_group("Multiplication");

    group.bench_function("Schoolbook O(n^2)", |ben| {
        ben.iter(|| black_box(&a).full_mul(black_box(&b)))
    });

    group.bench_function("Karatsuba O(n^1.58)", |ben| {
        ben.iter(|| black_box(&a).mul_karatsuba(black_box(&b)))
    });

    group.finish();
}

criterion_group!(benches, mul_benchmark);
criterion_main!(benches);
