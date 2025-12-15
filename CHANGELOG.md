# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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
