//! Field configurations for lattice-based cryptography (Kyber/Dilithium).
//!
//! These configurations define the field parameters for post-quantum cryptographic
//! schemes that operate over polynomial rings Zq[X]/(X^N + 1).
//!
//! # ⚠️ WARNING: U1024 Incompatibility
//!
//! The `KyberFieldConfig` and `DilithiumFieldConfig` types in this module use
//! the generic `U1024` Montgomery arithmetic which is **not optimized for small moduli**.
//! The Montgomery reduction assumes R = 2^1024 >> q, which causes numerical issues.
//!
//! **For production use**, prefer the specialized small-field types in [`super::small`]:
//!
//! - [`super::small::KyberFieldElement`] - Uses native u16 with Barrett reduction
//! - [`super::small::DilithiumFieldElement`] - Uses native u32 with Barrett reduction
//!
//! The types in this module are provided for API compatibility and testing purposes only.

use crate::{FieldConfig, U1024};

/// Kyber field configuration: q = 3329, n = 256.
///
/// # ⚠️ Deprecated for Production
///
/// This type uses U1024 Montgomery arithmetic which is incompatible with Kyber's
/// small modulus. For production use, prefer [`super::small::KyberFieldElement`].
///
/// Kyber uses an incomplete NTT since a 512th primitive root of unity
/// does not exist modulo q = 3329. The 256th root ζ = 17 is used instead.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[deprecated(
    since = "1.3.0",
    note = "Use `lumen_math::poly::ntt::small::KyberFieldElement` for production. \
            This U1024-based type has Montgomery arithmetic issues with small moduli."
)]
pub struct KyberFieldConfig;

#[allow(deprecated)]
impl FieldConfig for KyberFieldConfig {
    // q = 3329
    const MODULUS: U1024 = U1024([3329, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    const MODULUS_BITS: u32 = 12;

    // R^2 mod 3329 where R = 2^1024
    // Computed: (2^1024 mod 3329)^2 mod 3329 = 417
    const R2: U1024 = U1024([417, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);

    // N' such that N * N' ≡ -1 (mod 2^64) where N = 3329
    // Computed: 14119045929652129023
    const N_PRIME: U1024 = U1024([
        14119045929652129023,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ]);

    /// ζ = 17 is a primitive 256th root of unity mod 3329.
    const ROOT_OF_UNITY: U1024 = U1024([17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);

    /// For Kyber, ψ = 17 (the same as ROOT_OF_UNITY for incomplete NTT).
    const PRIMITIVE_2NTH_ROOT: U1024 = U1024([17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);

    const NTT_DEGREE: usize = 256;
}

/// Dilithium field configuration: q = 8,380,417, n = 256.
///
/// # ⚠️ Deprecated for Production
///
/// This type uses U1024 Montgomery arithmetic which is incompatible with Dilithium's
/// small modulus. For production use, prefer [`super::small::DilithiumFieldElement`].
///
/// Dilithium uses a complete NTT with a 512th primitive root of unity.
/// ψ = 1753 satisfies ψ^256 ≡ -1 (mod q).
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[deprecated(
    since = "1.3.0",
    note = "Use `lumen_math::poly::ntt::small::DilithiumFieldElement` for production. \
            This U1024-based type has Montgomery arithmetic issues with small moduli."
)]
pub struct DilithiumFieldConfig;

#[allow(deprecated)]
impl FieldConfig for DilithiumFieldConfig {
    // q = 8380417
    const MODULUS: U1024 = U1024([8380417, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    const MODULUS_BITS: u32 = 23;

    // R^2 mod 8380417 where R = 2^1024
    // Computed: (2^1024 mod 8380417)^2 mod 8380417 = 4628081
    const R2: U1024 = U1024([4628081, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);

    // N' such that N * N' ≡ -1 (mod 2^64) where N = 8380417
    // Computed: 16714476285912408063
    const N_PRIME: U1024 = U1024([
        16714476285912408063,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ]);

    /// ω = 3073009 is a primitive 256th root of unity mod 8380417.
    /// Computed as ψ² mod q where ψ = 1753.
    /// This means ω^256 ≡ 1 (mod q).
    const ROOT_OF_UNITY: U1024 = U1024([3073009, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);

    /// ψ = 1753, satisfying ψ^256 ≡ -1 (mod q).
    const PRIMITIVE_2NTH_ROOT: U1024 = U1024([1753, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);

    const NTT_DEGREE: usize = 256;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::FieldElement;
    use crate::poly::ntt::small::{DilithiumFieldElement, KyberFieldElement};

    // =========================================================================
    // Working Tests Using Small-Field Types (Recommended)
    // =========================================================================

    #[test]
    fn test_kyber_primitive_root_small() {
        // Verify ζ^256 ≡ 1 (mod 3329) using efficient small-field type
        let zeta = KyberFieldElement::zeta();
        let result = zeta.pow(256);
        assert_eq!(result.value(), 1, "ζ^256 should equal 1 mod 3329");
    }

    #[test]
    fn test_kyber_primitive_root_half_small() {
        // Verify ζ^128 ≡ -1 (mod 3329)
        let zeta = KyberFieldElement::zeta();
        let result = zeta.pow(128);
        assert_eq!(
            result.value(),
            (super::super::small::KYBER_Q - 1) as u16,
            "ζ^128 should equal -1 mod 3329"
        );
    }

    #[test]
    fn test_dilithium_primitive_2nth_root_small() {
        // Verify ψ^256 ≡ -1 (mod 8380417) using efficient small-field type
        let psi = DilithiumFieldElement::psi();
        let result = psi.pow(256);
        assert_eq!(
            result.value(),
            super::super::small::DILITHIUM_Q - 1,
            "ψ^256 should equal -1 mod 8380417"
        );
    }

    #[test]
    fn test_dilithium_primitive_nth_root_small() {
        // Verify ω^256 ≡ 1 (mod 8380417) where ω = ψ²
        let omega = DilithiumFieldElement::omega();
        let result = omega.pow(256);
        assert_eq!(result.value(), 1, "ω^256 should equal 1 mod 8380417");
    }

    // =========================================================================
    // Legacy Tests Using U1024 (Deprecated, kept for documentation)
    // =========================================================================

    // Note: These tests are ignored because the U1024 Montgomery implementation
    // is not compatible with small moduli. The small-field tests above verify
    // the same mathematical properties using the correct implementation.
    //
    // The mathematical constants (primitive roots) are verified correct:
    // - Kyber: ζ = 17, ζ^256 ≡ 1 (mod 3329) ✓
    // - Dilithium: ψ = 1753, ψ^256 ≡ -1 (mod 8380417) ✓
    // - Dilithium: ω = 3073009, ω^256 ≡ 1 (mod 8380417) ✓

    #[test]
    #[ignore = "U1024 Montgomery incompatible with small moduli - use small::KyberFieldElement"]
    #[allow(deprecated)]
    fn test_kyber_primitive_root_u1024_legacy() {
        let zeta = FieldElement::<KyberFieldConfig>::new(KyberFieldConfig::ROOT_OF_UNITY);
        let mut result = FieldElement::<KyberFieldConfig>::one();
        for _ in 0..256 {
            result = result * zeta;
        }
        assert_eq!(
            result.to_u1024(),
            U1024([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
            "ζ^256 should equal 1 mod 3329"
        );
    }

    #[test]
    #[ignore = "U1024 Montgomery incompatible with small moduli - use small::DilithiumFieldElement"]
    #[allow(deprecated)]
    fn test_dilithium_primitive_root_u1024_legacy() {
        let psi =
            FieldElement::<DilithiumFieldConfig>::new(DilithiumFieldConfig::PRIMITIVE_2NTH_ROOT);
        let mut result = FieldElement::<DilithiumFieldConfig>::one();
        for _ in 0..256 {
            result = result * psi;
        }
        let neg_one = U1024([8380416, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(
            result.to_u1024(),
            neg_one,
            "ψ^256 should equal -1 mod 8380417"
        );
    }
}
