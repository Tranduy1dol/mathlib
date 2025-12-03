# mathlib

[![codecov](https://codecov.io/gh/Tranduy1dol/mathlib/graph/badge.svg?token=S88FB34UD6)](https://codecov.io/gh/Tranduy1dol/mathlib)

A high-performance mathematical library for Rust, designed for cryptographic applications such as Zero-Knowledge Proofs (ZKPs) and Post-Quantum Cryptography (PQC).

## Features

- **Big Integer Arithmetic**: Efficient implementation of 1024-bit integers (`U1024`) with support for basic arithmetic operations.
- **Finite Fields**: Modular arithmetic using Montgomery reduction for fast field operations.
- **Polynomial Arithmetic**: Dense polynomial operations including addition, multiplication, and evaluation.
- **Number Theoretic Transform (NTT)**: Fast polynomial multiplication using NTT (O(n log n)) with Cooley-Tukey algorithm.
- **Hardware Acceleration**: AVX2 optimized backend for specific operations on x86_64 architectures (e.g., XOR, conditional selection).
- **GMP Integration**: Optional backend using GMP for verification and comparison (enabled via `gmp` feature).

## Installation

Add the following to your `Cargo.toml`:

```toml
[dependencies]
mathlib = { path = "." } # Or git repository URL
```

## Usage

### Big Integer Arithmetic

```rust
use mathlib::U1024;
use mathlib::traits::BigInt;

let a = U1024::from_u64(100);
let b = U1024::from_u64(200);
let (sum, carry) = a.carrying_add(&b);
assert_eq!(sum, U1024::from_u64(300));
```

### Field Arithmetic

```rust
use mathlib::U1024;
use mathlib::field::element::FieldElement;
use mathlib::field::constants::get_params;
use mathlib::traits::BigInt;

// Use pre-defined cryptographic parameters
let params = get_params();
let a = FieldElement::new(U1024::from_u64(5), params);
let b = FieldElement::new(U1024::from_u64(3), params);
let prod = a * b;
```

### Polynomial Operations

```rust
use mathlib::poly::dense::DensePolynomial;
use mathlib::field::element::FieldElement;
use mathlib::field::constants::get_params;
use mathlib::U1024;

let params = get_params();
let one = FieldElement::new(U1024::from_u64(1), params);
// Create polynomial P(x) = 1 + x
let poly = DensePolynomial::new(vec![one, one]);
```

## Architecture

The library is structured into several core modules:

- **`big_int`**: Implementation of fixed-size big integers (`U1024`). Includes backends for varying levels of optimization (Generic, AVX2, GMP).
- **`field`**: Finite field arithmetic implementations.
    - `montgomery`: Montgomery reduction parameters and algorithms.
    - `element`: `FieldElement` wrapper for modular arithmetic.
    - `constants`: Pre-defined field parameters.
- **`poly`**: Polynomial arithmetic.
    - `dense`: Dense polynomial representation and operations.
    - `ntt`: Number Theoretic Transform implementations.
- **`traits`**: Core traits defining the interface for big integers and fields.

## Performance

The library includes benchmarks using `criterion`. To run them:

```bash
cargo bench
```

Key performance features:
- **AVX2**: SIMD optimizations for bitwise operations and constant-time selection.
- **NTT**: Accelerates polynomial multiplication from O(n²) to O(n log n).
- **Montgomery Reduction**: Optimizes modular multiplication by avoiding expensive division.

## License

This project is licensed under the MIT License.