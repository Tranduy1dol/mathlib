use criterion::{Criterion, black_box, criterion_group, criterion_main};
use mathlib::field::constants::get_params;
use mathlib::field::element::FieldElement;
use mathlib::poly::dense::DensePolynomial;

fn bench_poly_mul(c: &mut Criterion) {
    let params = get_params();
    let size = 256;

    let coeffs = vec![FieldElement::one(params); size];
    let poly = DensePolynomial::new(coeffs);

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
