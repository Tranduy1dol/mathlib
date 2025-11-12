use std::hint::black_box;

use criterion::{Criterion, criterion_group, criterion_main};

use mathlib::num::int::u256::U256;

fn mul_benchmark(c: &mut Criterion) {
    let a = U256([
        0x12345678, 0x9ABCDEF0, 0xFEDCBA98, 0x76543210, 0x11111111, 0x22222222, 0x33333333,
        0x44444444,
    ]);
    let b = U256([
        0x55555555, 0x66666666, 0x77777777, 0x88888888, 0x99999999, 0xAAAAAAAA, 0xBBBBBBBB,
        0xCCCCCCCC,
    ]);

    let mut group = c.benchmark_group("U256 Multiplication");

    // Benchmark our fast O(n^2) base case
    group.bench_function("Schoolbook O(n^2) (Safe Rust)", |ben| {
        ben.iter(|| black_box(&a).full_mul_schoolbook_safe(black_box(&b)))
    });

    // Benchmark our new O(n^1.58) algorithm
    group.bench_function("Karatsuba O(n^1.58)", |ben| {
        ben.iter(|| black_box(&a).mul_karatsuba(black_box(&b)))
    });

    group.finish();
}

criterion_group!(benches, mul_benchmark);
criterion_main!(benches);
