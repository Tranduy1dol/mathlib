//! Field constants for cryptographic operations.
//!
//! This module provides pre-computed constants for a specific prime field,
//! including the field modulus and a primitive root of unity. These constants
//! are used for Number Theoretic Transform (NTT) operations and other field arithmetic.

use std::sync::OnceLock;

use crate::U1024;
use crate::field::montgomery::MontgomeryParams;

/// The prime field modulus P in hexadecimal representation.
///
/// This is a 1024-bit prime number that defines the finite field used for
/// cryptographic operations. The field has order P, and all arithmetic is
/// performed modulo this prime.
const P_HEX: &str = "CE6EA5DD0493C6624C9C46A40028DA8DA3806ED49484285FCF7EADB57DAFC72B208F713ED35A985798D6A7355AC37B178FF12C53B18BF607FE2B3C0F1C9043E77991FD00D889D6CBCA056F11DE9DF7D6D128AB0E5CE66F45CB916BD276235B46BD869AD0C0F159F1311C5D0DACE256DF2DA1E777ABDF69F072F3553D00000001";

/// A primitive root of unity in the field defined by P_HEX.
///
/// This value W is a generator element such that W^n = 1 (mod P) for some n,
/// where n is typically a power of 2. This root of unity is essential for
/// performing Number Theoretic Transform (NTT) operations efficiently.
const W_HEX: &str = "1D51F59721C38D3D48408329239882F49C5326F488D052C97E11C837FE04E79E1697A78F2AD3C4D7A7937DFDB2CD5E9146B7C23EAA626AEAD88C8DD9577AD3F6B21E34328BA550F5B488DA532323ABA51F3253D4D5510432095E2A57559BB6D5A28ADEDFAF36C9EE6560658AC1926B1C5544E9B534AEC34B8D9CCB77ACE9CC36";

/// Lazily initialized Montgomery parameters for the field.
///
/// This static variable holds the precomputed Montgomery parameters (modulus, R^2, n', and root of unity)
/// for efficient field arithmetic. It is initialized once on first access using `OnceLock`.
static PARAMS: OnceLock<MontgomeryParams> = OnceLock::new();

/// Returns a reference to the global Montgomery parameters for the field.
///
/// This function provides thread-safe, lazy initialization of the field parameters.
/// On the first call, it computes the Montgomery parameters from the hexadecimal constants
/// P_HEX and W_HEX. Subsequent calls return a cached reference to the same parameters.
///
/// # Returns
///
/// A static reference to `MontgomeryParams` containing:
/// - `modulus`: The prime field modulus P
/// - `r2`: R^2 mod P for Montgomery arithmetic
/// - `n_prime`: The Montgomery constant n' satisfying P * n' ≡ -1 (mod 2^1024)
/// - `root_of_unity`: A primitive root of unity W in the field
///
/// # Examples
///
/// ```
/// use mathlib::field::constants::get_params;
///
/// let params = get_params();
/// // Use params for field arithmetic operations
/// ```
pub fn get_params() -> &'static MontgomeryParams {
    PARAMS.get_or_init(|| {
        let modulus = U1024::from_hex(P_HEX);
        let root = U1024::from_hex(W_HEX);

        MontgomeryParams::new(modulus, root)
    })
}
