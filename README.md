# mathlib

[![codecov](https://codecov.io/gh/tranduy1dol/mathlib/branch/main/graph/badge.svg)](https://codecov.io/gh/tranduy1dol/mathlib)

---
## Day 1

---
- [Cpu Caches and Why You Care](https://www.youtube.com/watch?v=WDIkqP4JbkE)
- [What Every Programmer Should Know About Memory](https://www.akkadia.org/drepper/cpumemory.pdf)
- Cache Line/False Sharing/CPU Associated Effect
- Data-Oriented Design
- (Profiling) PGO, WPO

## Day 2

---
- `_mm256_add_epi64` and `_mm256_xor_si256` command
- [Branch Prediction](https://stackoverflow.com/questions/11227809/why-is-processing-a-sorted-array-faster-than-processing-an-unsorted-array)
- [Constant-Time Code](https://www.bearssl.org/constanttime.html)

## Day 3

---
- [`unsafe`](https://doc.rust-lang.org/nomicon/what-unsafe-does.html)
- `overflow_add`, `overflow_sub` implementations for `U256` type.
- `cargo asm 'mathlib::num::u256::U256::wrapping_add'`

## Day 4

---
- [`_mm256_xor_si256`](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#avxnewtechs=AVX2&ig_expand=7113)
- [`std::arch`](https://doc.rust-lang.org/std/arch/index.html)
- `#[target_feature(enable("avx2"))]` and Runtime Detection

## Day 5

---
- Implement `U256::full_mul`

## Day 6

---

- [Karatsuba multiplication](https://en.wikipedia.org/wiki/Karatsuba_algorithm)


## Day 7

---

- [Montgomery modular multiplication](https://en.wikipedia.org/wiki/Montgomery_modular_multiplication)


### Structure

---
```
mathlib/
├── Cargo.toml
├── src/
│   ├── lib.rs
│   │
│   ├── core/
│   │   ├── mod.rs
│   │   ├── field.rs
│   │   └── int.rs
│   │
│   ├── num/
│   │   ├── mod.rs
│   │   ├── int/
│   │   │   ├── mod.rs
│   │   │   └── u256.rs
│   │   │
│   │   └── prime_field/
│   │       ├── mod.rs
│   │       └── field_element.rs
│   │
│   └── arch/
│       ├── mod.rs
│       └── x86_64/
│           ├── mod.rs
│           └── avx2.rs
│
└── benches/
    └── field_add_bench.rs
```