use criterion::{Criterion, black_box, criterion_group, criterion_main};

use mathlib::big_int::backend::native;
use mathlib::{BigInt, U1024};

fn bench_add(c: &mut Criterion) {
    let a = U1024::from_u64(u64::MAX);
    let b = U1024::from_u64(1);

    let mut group = c.benchmark_group("Addition U1024");

    group.bench_function("GMP Add", |ben| ben.iter(|| black_box(a) + black_box(b)));

    group.bench_function("Native Add", |ben| {
        ben.iter(|| native::add(black_box(&a), black_box(&b)))
    });

    group.finish();
}

fn bench_xor(c: &mut Criterion) {
    let a = U1024::from_u64(u64::MAX);
    let b = U1024::from_u64(u64::MAX);

    let mut group = c.benchmark_group("Bitwise XOR U1024");

    group.bench_function("AVX2/Native Mixed", |ben| {
        ben.iter(|| black_box(a) ^ black_box(b))
    });

    group.finish();
}

criterion_group!(benches, bench_add, bench_xor);
criterion_main!(benches);
