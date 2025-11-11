use std::hint::black_box;

use criterion::{Criterion, criterion_group, criterion_main};

use mathlib::core::int::BigInt;
use mathlib::num::{int::u256::U256, prime_field::field_element::FieldElement};

/// Performs field element addition using an explicit carrying add and borrowing subtraction,
/// returning a normalized FieldElement reduced modulo the operand's modulus.
///
/// # Examples
///
/// ```
/// use mathlib::{FieldElement, U256};
///
/// let modulus = U256::from(97u64);
/// let a = FieldElement::new(U256::from(42u64), modulus);
/// let b = FieldElement::new(U256::from(60u64), modulus);
/// let _sum = field_add_naive(&a, &b);
/// ```
fn field_add_naive(a: &FieldElement, b: &FieldElement) -> FieldElement {
    let (sum, _carry) = a.inner.carrying_add(&b.inner);
    let (sum_norm, borrow) = sum.borrowing_sub(&a.modulus);

    let inner = if borrow { sum } else { sum_norm };
    FieldElement::new(inner, a.modulus)
}

/// Benchmarks two implementations of FieldElement addition: a naive branching version and a constant-time SIMD version.
///
/// Uses a fixed modulus and operand values to create two FieldElement instances, then runs both benchmarks in a Criterion group named "Field Addition".
///
/// # Examples
///
/// ```
/// use criterion::Criterion;
/// // In real use this function is passed to Criterion via the `criterion_group!` macro.
/// let mut c = Criterion::default();
/// field_add_benchmark(&mut c);
/// ```
fn field_add_benchmark(c: &mut Criterion) {
    let modulus = U256([u32::MAX; 8]);
    let a_val = U256([1, 2, 3, 4, 5, 6, 7, 8]);
    let b_val = U256([9, 1, 2, 3, 4, 5, 6, 7]);

    let a = FieldElement::new(a_val, modulus);
    let b = FieldElement::new(b_val, modulus);

    let mut group = c.benchmark_group("Field Addition");

    group.bench_function("Naive (branch-y) Add", |ben| {
        ben.iter(|| field_add_naive(black_box(&a), black_box(&b)))
    });

    group.bench_function("Constant-Time (SIMD) Add", |ben| {
        ben.iter(|| black_box(a) + black_box(b))
    });

    group.finish();
}

criterion_group!(benches, field_add_benchmark);
criterion_main!(benches);