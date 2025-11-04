# mathlib

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

### Structure

---
```
mathlib/
├── Cargo.toml
├── src/
│   ├── lib.rs
│   │
│   ├── arch/
│   │   ├── mod.rs
│   │   └── x86_64/
│   │       ├── mod.rs
│   │       └── avx2.rs
│   │
│   ├── num/
│   │   ├── mod.rs
│   │   ├── u256.rs
│   │   └── u512.rs
│   │
│   ├── field/
│   │   ├── mod.rs
│   │   └── montgomery.rs
│   │
│   └── poly/
│       ├── mod.rs
│       ├── fft.rs
│       └── ntt.rs
│
└── benches/
└── u256_arith.rs
```