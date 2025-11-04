use std::time::Instant;
use rand::prelude::SliceRandom;
use rand::thread_rng;

fn main() {
    // 1. Generate a large vector of random data
    let mut rng = thread_rng();
    let mut data: Vec<u8> = (0..=255).cycle().take(32 * 1024).collect();
    data.shuffle(&mut rng);

    // 2. Time the operation on unsorted (unpredictable) data
    let start_unsorted = Instant::now();
    let mut sum_unsorted: u64 = 0;
    for &item in &data {
        // The condition is unpredictable, leading to branch mispredictions
        if item > 128 {
            sum_unsorted += item as u64;
        }
    }
    let duration_unsorted = start_unsorted.elapsed();

    // 3. Sort the data to make it predictable
    data.sort_unstable();

    // 4. Time the operation on sorted (predictable) data
    let start_sorted = Instant::now();
    let mut sum_sorted: u64 = 0;
    for &item in &data {
        // The condition is predictable:
        // It will be 'false' for the first half and 'true' for the second half.
        // The CPU's branch predictor learns this pattern easily.
        if item > 128 {
            sum_sorted += item as u64;
        }
    }
    let duration_sorted = start_sorted.elapsed();

    // 5. Print the results
    println!("-- Branch Prediction Demo --");
    println!(
        "Unsorted (unpredictable) data took: {:.2?}",
        duration_unsorted
    );
    println!("Sorted (predictable) data took:   {:.2?}", duration_sorted);
    println!("\nSums (should be equal): {} vs {}", sum_unsorted, sum_sorted);

    // The sorted version should be significantly faster!
}