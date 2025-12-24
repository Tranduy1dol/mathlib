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
- **Cryptographic Protocols**: Implementation of Extended Euclidean Algorithm (GCD) and Chinese Remainder Theorem (CRT).
- **Signed Big Integers**: `I1024` type for signed 1024-bit arithmetic.

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

// Modular Arithmetic
let m = u1024!(17u64);
let res = a.mod_mul(&b, &m); // (100 * 200) % 17
```

### Signed Big Integers and Protocols

```rust
use mathlib::{i1024, I1024, U1024};
use mathlib::protocol::{extended_gcd, chinese_remainder_solver};

// Signed integers
let a = i1024!(10u64);
let b = i1024!(-20);
let diff = a - b; // 30

// Extended GCD
let u = U1024::from_u64(240);
let v = U1024::from_u64(46);
let gcd_res = extended_gcd(u, v);
// gcd_res.gcd == 2, u*x + v*y = gcd

// Chinese Remainder Theorem
let remainders = vec![U1024::from_u64(2), U1024::from_u64(3)];
let moduli = vec![U1024::from_u64(3), U1024::from_u64(5)];
// x = 2 mod 3, x = 3 mod 5 => x = 8
let result = chinese_remainder_solver(&remainders, &moduli).unwrap();
```

### Field Arithmetic

```rust
use mathlib::fp;

// Use the default field configuration
let a = fp!(5u64);
let b = fp!(3u64);
let prod = a * b;

// Or define a custom field
#[derive(mathlib::FieldConfig, Clone, Copy, Debug, Default, PartialEq, Eq)]
#[modulus = "0x11"] // modulus = 17
struct MyField;

let c = fp!(42u64, MyField);
```

### Polynomial Operations

```rust
use mathlib::{fp, DensePolynomial};

// Create field elements using the default field
let one = fp!(1u64);
let two = fp!(2u64);

// Create polynomial P(x) = 1 + 2x
let poly = DensePolynomial::new(vec![one, two]);

// Evaluate at a point
let x = fp!(5u64);
let y = poly.evaluate(&x);
```

## Architecture

The library is structured into several core modules:

- **`big_int`**: Implementation of fixed-size big integers (`U1024`). Includes backends for varying levels of optimization (Generic, AVX2, GMP).
- **`field`**: Finite field arithmetic implementations.
    - `montgomery`: Montgomery reduction parameters and algorithms.
    - `element`: `FieldElement` wrapper for modular arithmetic.
    - `config`: Field configuration trait and default parameters.
- **`poly`**: Polynomial arithmetic.
    - `dense`: Dense polynomial representation and operations.
    - `ntt`: Number Theoretic Transform implementations.
- **`protocol`**: Cryptographic primitives.
    - `gcd`: Extended Euclidean Algorithm.
    - `crt`: Chinese Remainder Theorem solver.
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