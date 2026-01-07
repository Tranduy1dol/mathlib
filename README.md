# lumen-math

[![CI](https://github.com/Tranduy1dol/lumen-math/actions/workflows/ci.yml/badge.svg)](https://github.com/Tranduy1dol/lumen-math/actions/workflows/ci.yml)
[![codecov](https://codecov.io/gh/Tranduy1dol/lumen-math/graph/badge.svg)](https://codecov.io/gh/Tranduy1dol/lumen-math)

> ✨ Part of the [luminescent](https://github.com/Tranduy1dol/luminescent) project — *Illuminating the path to zero-knowledge*

A high-performance mathematical library for Rust, designed for cryptographic applications such as Zero-Knowledge Proofs (ZKPs) and Post-Quantum Cryptography (PQC).

## Features

- **Big Integer Arithmetic**: Efficient implementation of 1024-bit integers (`U1024`) with support for basic arithmetic operations.
- **Finite Fields**: Modular arithmetic using Montgomery reduction for fast field operations.
- **Polynomial Arithmetic**: Dense polynomial operations including addition, multiplication, and evaluation.
- **Number Theoretic Transform (NTT)**: Fast polynomial multiplication using NTT (O(n log n)) with Cooley-Tukey algorithm.
- **Negacyclic NTT**: Specialized NTT for lattice-based cryptography (Kyber/Dilithium) over rings $Z_q[X]/(X^N + 1)$.
- **Small-Modulus Fields**: Optimized native `u32`/`u64` arithmetic with Barrett reduction for Kyber/Dilithium.
- **Ring Elements**: `RingElement<C>` with dual-state (coefficient/NTT) representation and lazy conversion.
- **Hardware Acceleration**: AVX2 optimized backend for specific operations on x86_64 architectures (e.g., XOR, conditional selection).
- **GMP Integration**: Optional backend using GMP for verification and comparison (enabled via `gmp` feature).
- **Cryptographic Protocols**: Implementation of Extended Euclidean Algorithm (GCD) and Chinese Remainder Theorem (CRT).
- **Signed Big Integers**: `I1024` type for signed 1024-bit arithmetic.

## Installation

Add the following to your `Cargo.toml`:

```toml
[dependencies]
lumen-math = { git = "https://github.com/Tranduy1dol/lumen-math" }
```

## Usage

### Big Integer Arithmetic

```rust
use lumen_math::{u1024, BigInt};

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
use lumen_math::{i1024, I1024, U1024};
use lumen_math::protocol::{extended_gcd, chinese_remainder_solver};

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

### Lattice-Based Cryptography (Kyber/Dilithium)

The library provides optimized field types for lattice-based schemes used in Post-Quantum Cryptography:

```rust
use lumen_math::poly::ntt::small::{KyberFieldElement, DilithiumFieldElement};

// Kyber (q = 3329) - Uses optimized u16 arithmetic
let k1 = KyberFieldElement::new(100);
let k2 = KyberFieldElement::new(200);
let k_prod = k1 * k2; // Efficient modular multiplication

// Dilithium (q = 8380417) - Uses optimized u32 arithmetic
let d1 = DilithiumFieldElement::new(12345);
let d2 = DilithiumFieldElement::new(67890);
let d_prod = d1 * d2;
```

### Ring Elements (Polynomial Rings)

For operations in polynomial rings $R_q = \mathbb{Z}_q[X]/(X^N + 1)$:

```rust
use lumen_math::{RingElement, NttContext, DefaultFieldConfig, fp};
use std::sync::Arc;

// Create shared NTT context
let ctx = Arc::new(NttContext::<DefaultFieldConfig>::new(256));

// Create ring elements
let a = RingElement::new(vec![fp!(1u64); 256], ctx.clone());
let b = RingElement::one(ctx);

// Arithmetic (auto-converts between coefficient/NTT forms)
let product = a * b;  // Uses NTT multiplication
```

### Field Arithmetic (Generic)

```rust
use lumen_math::fp;

// Use the default field configuration
let a = fp!(5u64);
let b = fp!(3u64);
let prod = a * b;

// Or define a custom field
#[derive(lumen_math::FieldConfig, Clone, Copy, Debug, Default, PartialEq, Eq)]
#[modulus = "0x11"] // modulus = 17
struct MyField;

let c = fp!(42u64, MyField);
```

### Polynomial Operations & NTT

```rust
use lumen_math::{fp, DensePolynomial};
use lumen_math::poly::ntt::{ntt, intt};

// Create field elements using the default field
let one = fp!(1u64);
let two = fp!(2u64);

// Create polynomial P(x) = 1 + 2x
let mut poly = vec![one, two]; // Coefficients

// Perform Number Theoretic Transform
ntt(&mut poly);

// Perform Inverse NTT
intt(&mut poly);
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
    - `ntt`: Number Theoretic Transform (cyclic and negacyclic) implementations.
        - `mod.rs`: Generic `NttContext` and re-exports.
        - `cyclic.rs`: Standard cyclic NTT over $Z_q[X]/(X^N-1)$.
        - `negacyclic.rs`: Negacyclic NTT over $Z_q[X]/(X^N+1)$.
        - `small.rs`: Specialized small-modulus field types.
- **`protocol`**: Cryptographic primitives.
    - `gcd`: Extended Euclidean Algorithm.
    - `crt`: Chinese Remainder Theorem solver.
- **`ring`**: Ring elements for lattice-based cryptography.
    - `element`: `RingElement<C>` with dual-state (coefficient/NTT) representation.
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