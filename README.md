# mathlib

---
## Day 1

---
- [Cpu Caches and Why You Care](https://www.youtube.com/watch?v=WDIkqP4JbkE)
- [What Every Programmer Should Know About Memory](https://www.akkadia.org/drepper/cpumemory.pdf)
- Cache Line/False Sharing/CPU Associated Effect
- Data-Oriented Design
- (Profiling) PGO, WPO

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