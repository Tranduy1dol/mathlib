use criterion::{Criterion, black_box, criterion_group, criterion_main};

use mathlib::U1024;
use mathlib::big_int::backend::native;

fn bench_add(c: &mut Criterion) {
    let a = U1024([
        0xFFFFFFFFFFFFFFFF,
        0x0000000000000000,
        0xFFFFFFFFFFFFFFFF,
        0x0000000000000000,
        0xFFFFFFFFFFFFFFFF,
        0x0000000000000000,
        0xFFFFFFFFFFFFFFFF,
        0x0000000000000000,
        0xFFFFFFFFFFFFFFFF,
        0x0000000000000000,
        0xFFFFFFFFFFFFFFFF,
        0x0000000000000000,
        0xFFFFFFFFFFFFFFFF,
        0x0000000000000000,
        0xFFFFFFFFFFFFFFFF,
        0x0000000000000000,
    ]);

    let b = U1024([
        0x0123456789ABCDEF,
        0xFEDCBA9876543210,
        0x0123456789ABCDEF,
        0xFEDCBA9876543210,
        0x0123456789ABCDEF,
        0xFEDCBA9876543210,
        0x0123456789ABCDEF,
        0xFEDCBA9876543210,
        0x0123456789ABCDEF,
        0xFEDCBA9876543210,
        0x0123456789ABCDEF,
        0xFEDCBA9876543210,
        0x0123456789ABCDEF,
        0xFEDCBA9876543210,
        0x0123456789ABCDEF,
        0xFEDCBA9876543210,
    ]);

    let mut group = c.benchmark_group("Addition U1024");

    #[cfg(feature = "gmp")]
    group.bench_function("GMP Add", |ben| ben.iter(|| black_box(a) + black_box(b)));

    group.bench_function("Native Add", |ben| {
        ben.iter(|| native::add(black_box(&a), black_box(&b)))
    });

    group.finish();
}

fn bench_xor(c: &mut Criterion) {
    let a = U1024([
        0xAAAAAAAAAAAAAAAA,
        0x5555555555555555,
        0xAAAAAAAAAAAAAAAA,
        0x5555555555555555,
        0xAAAAAAAAAAAAAAAA,
        0x5555555555555555,
        0xAAAAAAAAAAAAAAAA,
        0x5555555555555555,
        0xAAAAAAAAAAAAAAAA,
        0x5555555555555555,
        0xAAAAAAAAAAAAAAAA,
        0x5555555555555555,
        0xAAAAAAAAAAAAAAAA,
        0x5555555555555555,
        0xAAAAAAAAAAAAAAAA,
        0x5555555555555555,
    ]);

    let b = U1024([
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        0x0000000000000000,
        0x0000000000000000,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        0x0000000000000000,
        0x0000000000000000,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        0x0000000000000000,
        0x0000000000000000,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        0x0000000000000000,
        0x0000000000000000,
    ]);

    let mut group = c.benchmark_group("Bitwise XOR U1024");

    group.bench_function("AVX2/Native Mixed", |ben| {
        ben.iter(|| black_box(a) ^ black_box(b))
    });

    group.finish();
}

criterion_group!(benches, bench_add, bench_xor);
criterion_main!(benches);
