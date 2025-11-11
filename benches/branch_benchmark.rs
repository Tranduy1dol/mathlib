use std::hint::black_box;

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use rand::prelude::*;

const DATA_SIZE: usize = 32 * 1024;

/// Sums numbers greater than 128 using a standard conditional branch.
fn branchy_sum(data: &[u8]) -> u64 {
    let mut sum: u64 = 0;
    for &item in data {
        if item > 128 {
            sum += item as u64;
        }
    }
    sum
}

/// Sums numbers greater than 128 using a branch-free technique.
/// This avoids conditional jumps, which can be faster on unpredictable data.
fn branchless_sum(data: &[u8]) -> u64 {
    let mut sum: u64 = 0;
    for &item in data {
        // The comparison `(item > 128)` evaluates to a boolean (1 or 0).
        // We multiply the item by this result.
        // - If true (1): `sum += item * 1`
        // - If false (0): `sum += item * 0`
        // The compiler turns this into `cmov` (conditional move) instructions
        // instead of conditional jumps, avoiding pipeline flushes.
        sum += (item as u64) * (item > 128) as u64;
    }
    sum
}

/// Benchmarks branchy and branchless summation implementations on both predictable (sorted)
/// and unpredictable (shuffled) byte data to compare the effect of branch prediction.
///
/// The function prepares a shuffled byte buffer and a sorted clone, then measures
/// four cases in a Criterion benchmark group named "Branch Prediction Comparison":
/// branchy and branchless implementations on unsorted (unpredictable) and sorted
/// (predictable) inputs.
///
/// # Examples
///
/// ```
/// use criterion::{criterion_group, criterion_main, Criterion};
///
/// // Register the benchmark so Criterion can run it.
/// criterion_group!(benches, branch_prediction_benchmark);
/// criterion_main!(benches);
/// ```
///
/// # Parameters
///
/// - `c`: Criterion benchmark context provided by the Criterion harness.
fn branch_prediction_benchmark(c: &mut Criterion) {
    // --- Setup ---
    // Generate a vector of random data.
    let mut rng = rand::thread_rng();
    let mut unsorted_data: Vec<u8> = (0..=255).cycle().take(DATA_SIZE).collect();
    unsorted_data.shuffle(&mut rng);

    // Create a sorted version of the same data.
    let mut sorted_data = unsorted_data.clone();
    sorted_data.sort_unstable();

    // --- Benchmarking ---
    let mut group = c.benchmark_group("Branch Prediction Comparison");

    // Benchmark on unsorted (unpredictable) data
    group.bench_function(BenchmarkId::new("Branchy", "Unsorted"), |b| {
        b.iter(|| branchy_sum(black_box(&unsorted_data)))
    });

    group.bench_function(BenchmarkId::new("Branchless", "Unsorted"), |b| {
        b.iter(|| branchless_sum(black_box(&unsorted_data)))
    });

    // Benchmark on sorted (predictable) data
    group.bench_function(BenchmarkId::new("Branchy", "Sorted"), |b| {
        b.iter(|| branchy_sum(black_box(&sorted_data)))
    });

    group.bench_function(BenchmarkId::new("Branchless", "Sorted"), |b| {
        b.iter(|| branchless_sum(black_box(&sorted_data)))
    });

    group.finish();
}

criterion_group!(benches, branch_prediction_benchmark);
criterion_main!(benches);