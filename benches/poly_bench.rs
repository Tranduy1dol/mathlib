use criterion::{Criterion, black_box, criterion_group, criterion_main};
use mathlib::{DefaultFieldConfig, FieldElement, Polynomial};

fn bench_poly_mul(c: &mut Criterion) {
    let size = 256;

    // Use DefaultFieldConfig instead of get_params()
    let coeffs = vec![FieldElement::<DefaultFieldConfig>::one(); size];
    let poly = Polynomial::new(coeffs);

    let mut group = c.benchmark_group("Polynomial Multiplication (Deg 256)");

    group.bench_function("Naive Mul", |b| {
        b.iter(|| black_box(&poly).clone() * black_box(&poly).clone())
    });

    group.bench_function("NTT Mul", |b| {
        b.iter(|| black_box(&poly).mul_fast(black_box(&poly)))
    });

    group.finish();
}

criterion_group!(benches, bench_poly_mul);
criterion_main!(benches);
