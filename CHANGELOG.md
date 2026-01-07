# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [1.4.0] - 2026-01-06

### Added

- **Ring Element for Lattice Cryptography**: New `RingElement<C>` type for polynomials in $R_q = \mathbb{Z}_q[X]/(X^N + 1)$
  - **Dual-state representation**: Coefficient form ↔ NTT form with lazy conversion
  - **Arithmetic operations**: `Add`, `Sub`, `Mul`, `Neg` for both owned and reference types
  - **State management**: `to_ntt()`, `to_coefficient()`, `into_ntt()`, `into_coefficient()`
  - **Shared context**: Uses `Arc<NttContext<C>>` for efficient NTT table sharing
  - **Query methods**: `state()`, `coefficients()`, `ntt_values()`, `is_zero()`, `scale()`
  - Exports: `RingElement`, `RingElementState` from `lumen_math::ring`

### Improved

- **Public ring module**: `lumen_math::ring` is now public for direct access

## [1.3.0] - 2025-12-30

### Changed

- **Rebranding to Luminescent**: Renamed package from `mathlib` to `lumen-math`
  - Now part of the [luminescent](https://github.com/Tranduy1dol/luminescent) project
  - Updated all import paths: `mathlib::*` → `lumen_math::*`
  - Macros crate renamed from `mathlib_macros` to `lumen-math-macros`
  - Repository URL changed to `https://github.com/Tranduy1dol/lumen-math`

### Added

- **Lattice-Based Cryptography Support**:
  - **Negacyclic NTT**: Specialized NTT for Kyber/Dilithium over $Z_q[X]/(X^N + 1)$
  - **Small-Modulus Fields**: Optimized `u16`/`u32` arithmetic with Barrett reduction
    - `KyberFieldElement` (q=3329)
    - `DilithiumFieldElement` (q=8380417)
  - **`NttContext`**: Precomputed tables for efficient batch NTT operations

- **Documentation**:
  - **THEORY.md**: Comprehensive mathematical documentation with LaTeX formulas
  - Updated README with lattice-crypto examples

### Fixed

- **NTT Correctness**: Fixed twiddle factor calculation for arbitrary moduli (was hardcoded for 2^32 roots)
- **Dilithium Parameters**: Corrected `ROOT_OF_UNITY` and `ω` constants
- **API Safety**: Made `NttContext::mul` non-mutating by default (added `mul_in_place` for efficiency)

### Deprecated

- **U1024-based Lattice Configs**: `KyberFieldConfig` and `DilithiumFieldConfig` are deprecated in favor of the new optimized `lumen_math::poly::ntt::small` types

### Migration Guide

```rust
// Old (mathlib)
use mathlib::{u1024, fp, BigInt};
use mathlib::protocol::extended_gcd;

// New (lumen-math)
use lumen_math::{u1024, fp, BigInt};
use lumen_math::protocol::extended_gcd;
```

## [1.2.0] - 2025-12-24

### Added

- **Signed Big Integer `I1024`**: New signed 1024-bit integer type
  - Magnitude + sign representation for negative value support
  - Full arithmetic: `Add`, `Sub`, `Mul`, `Neg`
  - `sub_mul()` optimized for Extended Euclidean Algorithm
  - `i1024!` macro for convenient construction
  - Used by `ExtendedGcdResult` for Bézout coefficients

- **`Digest` Trait**: New trait for hash-to-value operations
  - `from_hash(input: &[u8])` - Hash bytes to a cryptographic type
  - `from_hash_with_domain(domain, input)` - Hash with domain separation
  - Implemented for `U1024` and `FieldElement<C>`
  - Uses RFC 9380 `expand_message_xmd` for constant-time, unbiased hashing

- **Modular Arithmetic Methods on `U1024`**:
  - `mod_mul(&self, other, modulus)` - Modular multiplication with 2048-bit intermediate
  - `mod_pow(&self, exp, modulus)` - Modular exponentiation (square-and-multiply)
  - `cge(&self, exp, modulus)` - Alias for mod_pow (cyclic group exponentiation)

- **`protocol` Module**: New module for cryptographic protocols
  - `protocol::gcd` - Extended Euclidean Algorithm
    - `extended_gcd(a, b)` returns `ExtendedGcdResult` with GCD and Bézout coefficients
    - `mod_inverse(a, m)` computes multiplicative inverse
  - `protocol::crt` - Chinese Remainder Theorem
    - `chinese_remainder_solver(remainders, moduli)` solves congruence systems
    - `chinese_remainder(a1, n1, a2, n2)` convenience wrapper for two congruences
    - `CrtError` enum for error handling

### Improved

- **Cleaner Import Paths**:
  - `use mathlib::protocol::{extended_gcd, chinese_remainder};`
  - `use mathlib::{U1024, I1024, Digest};`

### Migration Guide

```rust
// Old (1.1.0)
use mathlib::algorithms::{extended_gcd, mod_pow, hash_to_field};
let result = mod_pow(base, exp, modulus);
let fe: FieldElement<C> = hash_to_field(b"data");

// New (1.2.0)
use mathlib::protocol::extended_gcd;
use mathlib::{U1024, Digest, FieldElement};
let result = base.mod_pow(&exp, &modulus);
let fe = FieldElement::<C>::from_hash(b"data");
```

## [1.1.0] - 2025-12-21

### Added

- **Enhanced Polynomial Module**: ZK-STARK-style polynomial operations
  - **`Polynomial<C>`**: Unified univariate polynomial with comprehensive operations:
    - `divide_with_remainder()` - Polynomial long division
    - `interpolate()` - Lagrange interpolation
    - `derivative()` - Formal derivative computation
    - `zerofier()` - Create vanishing polynomials
    - `compose()` - Polynomial composition
    - `scale()` / `shift()` - Coefficient transformations
    - `evaluate_batch()` - Multi-point evaluation
    - `mul_ntt()` / `mul_fast()` - NTT-based fast multiplication
  - **`MultivariatePolynomial<C>`**: Multivariate polynomial support:
    - Sparse representation using `BTreeMap`
    - Arbitrary number of variables
    - `partial_evaluate()` - Partially fix variables
    - `degree_in()` / `total_degree()` - Degree tracking
    - Conversion to/from univariate polynomials
  - **Mathematical Display**: Polynomials display as `3x^2 + 2x + 1`

- **U1024 Byte Conversion Methods**:
  - `to_le_bytes()` - Convert to 128-byte little-endian array
  - `to_be_bytes()` - Convert to 128-byte big-endian array
  - Complements existing `from_le_bytes()` and `from_be_bytes()`

### Changed

- **Refactored `DensePolynomial`**: Now a type alias for `Polynomial`
  - Eliminates ~200 lines of duplicate code
  - All `DensePolynomial` code continues to work unchanged
  - `mul_fast()` method preserved for backward compatibility

### Improved

- **Comprehensive Integration Tests**: 30+ new polynomial tests
  - Univariate: arithmetic, division, interpolation, derivative, zerofier
  - Multivariate: evaluation, partial evaluation, degree tracking
  - Cross-type: consistency between univariate and multivariate

## [1.0.0] - 2025-12-19

### ⚠️ BREAKING CHANGES

- **FieldElement Refactored to Use Type-Level Configuration**:
  - Changed from `FieldElement<'a>` to `FieldElement<C: FieldConfig>`
  - Removed lifetime parameters - field elements are now `'static`
  - Field parameters moved from runtime references to compile-time type parameters
  - Breaking change to `fp!` macro signature: `fp!(val, &params)` → `fp!(val)` or `fp!(val, ConfigType)`

### Added

- **`FieldConfig` Trait**: New trait for compile-time field configuration
  - Contains `MODULUS`, `R2`, `N_PRIME`, `ROOT_OF_UNITY`, and `MODULUS_BITS` as associated constants
  - Enables zero-cost field element construction
  
- **`const fn` Constructors**: Field elements can now be constructed at compile time
  - `FieldElement::new()` - `const fn` for compile-time initialization
  - `FieldElement::zero()` - `const fn` 
  - `FieldElement::one()` - `const fn`
  - `FieldElement::from_montgomery()` - `const fn`

- **Const Arithmetic for U1024**: Added compile-time arithmetic operations
  - `const_add()`, `const_sub()`, `const_mul()` for const contexts
  - Enables compile-time field element calculations
  - Zero runtime cost - all computation happens at compile time

- **Proc-Macro for Field Configuration**: New `mathlib_macros` crate
  - `#[derive(FieldConfig)]` - Automatically implement `FieldConfig` from modulus
  - Computes `R2` and `N_PRIME` at compile time during macro expansion
  - Usage: `#[derive(FieldConfig)] #[modulus = "0x..."] struct MyField;`

- **Utility Functions**: Exported Montgomery parameter computation
  - `compute_r2(modulus: &U1024) -> U1024` - Compute R² mod P
  - `compute_n_prime(modulus: &U1024) -> U1024` - Compute N' for Montgomery reduction
  - Both use native `U1024` type instead of external BigInt

- **`DefaultFieldConfig`**: Pre-configured field for standard cryptographic parameters

### Changed

- **Renamed**: `MontgomeryParams` → `MontgomeryContext` for clarity
- **Generic Polynomials**: `DensePolynomial<'a>` → `DensePolynomial<C: FieldConfig>`
- **Generic NTT**: `ntt()` and `intt()` functions are now generic over `C: FieldConfig`
- **Updated Tests**: All tests migrated to new API with example field configurations
- **Updated Benchmarks**: Benchmarks now use `DefaultFieldConfig` instead of deprecated `get_params()`

### Removed

- **Deprecated `constants` module**: Removed `src/field/constants.rs` and `get_params()` function
  - All functionality replaced by `DefaultFieldConfig`
  - Eliminates code duplication
  - Cleaner API with single source of truth for field parameters

### Improved

- **Comprehensive Test Coverage**: Added 55+ new tests (76 total tests)
  - **Field Element Tests**: 14 tests covering arithmetic, properties, and edge cases
  - **Polynomial Tests**: 13 tests for operations, evaluation, and NTT comparison
  - **NTT Tests**: 10 tests for various sizes, edge cases, and correctness
  - **U1024 Tests**: 18 tests for const arithmetic and all operations
  - All tests pass with zero warnings via `cargo clippy`

## [0.4.0] - 2025-12-15

### Added

- **FieldElement Enhancements**: Added missing features to `FieldElement`:
  - `Neg` trait - Unary negation operator (`-a`) for field elements
  - `is_zero()` - Check if a field element is zero
  - `double()` - Efficiently compute `2 * self`
  - `square()` - Efficiently compute `self * self`

These additions improve compatibility with downstream libraries and provide a more complete field element API.

## [0.3.0] - 2025-12-15

### Added

- **Macro System**: Introduced powerful macros for cleaner, more ergonomic code:
  - `u1024!`: Create `U1024` values from primitives (u8, u16, u32, u64, u128), hex strings, or arrays
  - `mont!`: Create `MontgomeryParams` with minimal boilerplate  
  - `fp!`: Create `FieldElement` values elegantly
  
- **Convenience Methods**: Added `from_*` methods for U1024:
  - `from_u8()`, `from_u16()`, `from_u32()`, `from_u128()`
  - `from_bits()` - create from boolean array
  - `from_le_bytes()` - create from little-endian bytes
  - `from_be_bytes()` - create from big-endian bytes

### Changed

- Updated all documentation examples to use the new macro-based API
- Simplified imports across all examples - macros reduce boilerplate significantly

### Performance

- No performance impact - macros expand to the same underlying code
- Zero-cost abstractions maintain the same efficiency as before

## [0.2.2] - Previous Release

Initial release with core functionality:
- U1024 big integer arithmetic
- Montgomery field arithmetic
- Dense polynomial operations
- Number Theoretic Transform (NTT)
- AVX2 and GMP backend support
