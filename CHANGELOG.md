# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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

For migration instructions, see [migration_guide.md](migration_guide.md).


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
