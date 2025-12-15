# mathlib

[![CI](https://github.com/Tranduy1dol/mathlib/actions/workflows/ci.yml/badge.svg)](https://github.com/Tranduy1dol/mathlib/actions/workflows/ci.yml)
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
use mathlib::{u1024, BigInt};

// Create U1024 values using the u1024! macro
let a = u1024!(100u64);
let b = u1024!(200u64);
let (sum, carry) = a.carrying_add(&b);
assert_eq!(sum, u1024!(300u64));

// From hex strings
let c = u1024!("0xDEADBEEF");

// From arrays
let d = u1024!([1, 2, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
```

### Field Arithmetic

```rust
use mathlib::{fp, mont, u1024, get_params};

// Create Montgomery parameters using the mont! macro
let params = mont!(17u64, 2u64);

// Create field elements using the fp! macro
let a = fp!(5u64, &params);
let b = fp!(3u64, &params);
let prod = a * b;

// Or use pre-defined cryptographic parameters
let params = get_params();
let c = fp!(42u64, params);
```

### Polynomial Operations

```rust
use mathlib::{fp, DensePolynomial, get_params};

let params = get_params();

// Create field elements using the fp! macro
let one = fp!(1u64, params);
let two = fp!(2u64, params);

// Create polynomial P(x) = 1 + 2x
let poly = DensePolynomial::new(vec![one, two]);

// Evaluate at a point
let x = fp!(5u64, params);
let y = poly.evaluate(&x);
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