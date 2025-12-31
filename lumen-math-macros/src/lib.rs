use num_bigint::BigUint;
use num_traits::{Num, One};
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput, Expr, Lit, Meta};

fn biguint_to_u64_array(v: &BigUint) -> [u64; 16] {
    let mut arr = [0u64; 16];
    let bytes = v.to_bytes_le();
    for (i, chunk) in bytes.chunks(8).enumerate() {
        if i >= 16 {
            break;
        }
        let mut buf = [0u8; 8];
        buf[..chunk.len()].copy_from_slice(chunk);
        arr[i] = u64::from_le_bytes(buf);
    }
    arr
}

fn u64_array_to_tokens(arr: &[u64; 16]) -> proc_macro2::TokenStream {
    let content = arr.iter().map(|&x| quote! { #x });
    quote! {
        lumen_math::U1024([#(#content),*])
    }
}

/// Compute modular inverse of P modulo 2^1024 using bit-by-bit lifting.
/// This mirrors the logic in MontgomeryContext::compute_n_prime.
fn compute_n_prime_bigint(modulus: &BigUint) -> BigUint {
    let mut inv = BigUint::one();

    for i in 1..1024 {
        let p_inv = modulus * &inv;
        if p_inv.bit(i) {
            inv.set_bit(i, true);
        }
    }

    // N' = -inv mod R = R - inv where R = 2^1024
    let r_val = BigUint::one() << 1024;
    &r_val - &inv
}

/// Compute R^2 mod P where R = 2^1024.
/// This mirrors the logic in MontgomeryContext::compute_r2.
fn compute_r2_bigint(modulus: &BigUint) -> BigUint {
    // Compute 2^2048 mod P
    let two = BigUint::from(2u32);
    two.modpow(&BigUint::from(2048u32), modulus)
}

#[proc_macro_derive(FieldConfig, attributes(modulus, root))]
pub fn derive_field_config(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;

    let mut modulus_str = None;
    let mut root_str = None;

    for attr in input.attrs {
        if attr.path().is_ident("modulus") {
            if let Meta::NameValue(nv) = &attr.meta {
                if let Expr::Lit(expr_lit) = &nv.value {
                    if let Lit::Str(lit) = &expr_lit.lit {
                        modulus_str = Some(lit.value());
                    }
                }
            }
        } else if attr.path().is_ident("root") {
            if let Meta::NameValue(nv) = &attr.meta {
                if let Expr::Lit(expr_lit) = &nv.value {
                    if let Lit::Str(lit) = &expr_lit.lit {
                        root_str = Some(lit.value());
                    }
                }
            }
        }
    }

    let modulus_hex = modulus_str.expect("FieldConfig: #[modulus = \"...\"] attribute is required");
    let clean_hex = modulus_hex.strip_prefix("0x").unwrap_or(&modulus_hex);
    let modulus = BigUint::from_str_radix(clean_hex, 16).expect("Invalid hex string for modulus");

    // Validate that modulus is odd (required for Montgomery arithmetic)
    if !modulus.bit(0) {
        panic!("FieldConfig: modulus must be odd for Montgomery arithmetic");
    }

    // Compute R2 and N_PRIME
    let r2 = compute_r2_bigint(&modulus);
    let n_prime = compute_n_prime_bigint(&modulus);

    // Handle root
    let root = if let Some(s) = root_str {
        let clean = s.strip_prefix("0x").unwrap_or(&s);
        BigUint::from_str_radix(clean, 16).expect("Invalid hex for root")
    } else {
        BigUint::one()
    };

    let modulus_arr = biguint_to_u64_array(&modulus);
    let r2_arr = biguint_to_u64_array(&r2);
    let n_prime_arr = biguint_to_u64_array(&n_prime);
    let root_arr = biguint_to_u64_array(&root);

    let modulus_tokens = u64_array_to_tokens(&modulus_arr);
    let r2_tokens = u64_array_to_tokens(&r2_arr);
    let n_prime_tokens = u64_array_to_tokens(&n_prime_arr);
    let root_tokens = u64_array_to_tokens(&root_arr);

    let expanded = quote! {
        impl lumen_math::field::config::FieldConfig for #name {
            const MODULUS: lumen_math::U1024 = #modulus_tokens;
            const MODULUS_BITS: u32 = 1024;
            const R2: lumen_math::U1024 = #r2_tokens;
            const N_PRIME: lumen_math::U1024 = #n_prime_tokens;
            const ROOT_OF_UNITY: lumen_math::U1024 = #root_tokens;

            fn to_montgomery_context() -> lumen_math::field::montgomery::MontgomeryContext {
                 lumen_math::field::montgomery::MontgomeryContext {
                     modulus: Self::MODULUS,
                     r2: Self::R2,
                     n_prime: Self::N_PRIME,
                     root_of_unity: Self::ROOT_OF_UNITY,
                 }
            }
        }
    };

    TokenStream::from(expanded)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_biguint_to_u64_array_small() {
        let value = BigUint::from(42u64);
        let arr = biguint_to_u64_array(&value);

        assert_eq!(arr[0], 42);
        for i in 1..16 {
            assert_eq!(arr[i], 0, "Limb {} should be zero", i);
        }
    }

    #[test]
    fn test_biguint_to_u64_array_large() {
        let value = BigUint::from_str_radix("FFFFFFFFFFFFFFFF", 16).unwrap();
        let arr = biguint_to_u64_array(&value);

        assert_eq!(arr[0], u64::MAX);
        for i in 1..16 {
            assert_eq!(arr[i], 0, "Limb {} should be zero", i);
        }
    }

    #[test]
    fn test_biguint_to_u64_array_multi_limb() {
        // Create a value that spans multiple limbs
        let mut value = BigUint::from(u64::MAX);
        value = (value << 64) + BigUint::from(12345u64);

        let arr = biguint_to_u64_array(&value);

        assert_eq!(arr[0], 12345);
        assert_eq!(arr[1], u64::MAX);
        for i in 2..16 {
            assert_eq!(arr[i], 0, "Limb {} should be zero", i);
        }
    }

    #[test]
    fn test_biguint_to_u64_array_zero() {
        let value = BigUint::from(0u64);
        let arr = biguint_to_u64_array(&value);

        for i in 0..16 {
            assert_eq!(arr[i], 0, "All limbs should be zero");
        }
    }

    #[test]
    fn test_compute_n_prime_for_17() {
        // Test with modulus = 17
        let modulus = BigUint::from(17u64);
        let n_prime = compute_n_prime_bigint(&modulus);

        // N' should satisfy: P * N' ≡ -1 (mod 2^1024)
        // Which means: P * N' + 1 ≡ 0 (mod 2^1024)
        let product = &modulus * &n_prime;
        let plus_one = product + BigUint::one();
        let r = BigUint::one() << 1024;
        let remainder = plus_one % r;

        assert_eq!(
            remainder,
            BigUint::from(0u64),
            "P * N' + 1 should be divisible by R"
        );
    }

    #[test]
    fn test_compute_r2_for_17() {
        // Test with modulus = 17
        let modulus = BigUint::from(17u64);
        let r2 = compute_r2_bigint(&modulus);

        // R^2 mod 17 should equal ((2^1024)^2) mod 17
        // For small modulus like 17, we can verify: 2^2048 mod 17
        let expected = BigUint::from(2u32).modpow(&BigUint::from(2048u32), &modulus);

        assert_eq!(r2, expected);
    }

    #[test]
    fn test_compute_r2_result_less_than_modulus() {
        // Verify that R^2 mod P is always < P
        let test_moduli = vec![
            BigUint::from(17u64),
            BigUint::from(97u64),
            BigUint::from(65521u64), // Large prime
        ];

        for modulus in test_moduli {
            let r2 = compute_r2_bigint(&modulus);
            assert!(r2 < modulus, "R^2 mod P should be less than P");
        }
    }

    #[test]
    fn test_compute_n_prime_properties() {
        // Test N' computation for various moduli
        let test_moduli = vec![
            BigUint::from(17u64),
            BigUint::from(97u64),
            BigUint::from(257u64),
        ];

        for modulus in test_moduli {
            let n_prime = compute_n_prime_bigint(&modulus);

            // Verify the property: P * N' + 1 ≡ 0 (mod R)
            let product = &modulus * &n_prime;
            let plus_one = product + BigUint::one();
            let r = BigUint::one() << 1024;
            let remainder = plus_one % r;

            assert_eq!(
                remainder,
                BigUint::from(0u64),
                "N' property failed for modulus {}",
                modulus
            );
        }
    }

    #[test]
    fn test_hex_parsing_with_0x_prefix() {
        // Test that both "0x11" and "11" parse correctly
        let with_prefix = "0x11";
        let without_prefix = "11";

        let clean_with = with_prefix.strip_prefix("0x").unwrap_or(with_prefix);
        let clean_without = without_prefix.strip_prefix("0x").unwrap_or(without_prefix);

        let val1 = BigUint::from_str_radix(clean_with, 16).unwrap();
        let val2 = BigUint::from_str_radix(clean_without, 16).unwrap();

        assert_eq!(val1, val2);
        assert_eq!(val1, BigUint::from(17u64));
    }

    #[test]
    fn test_biguint_roundtrip() {
        // Test that converting BigUint -> array -> BigUint preserves value
        let original = BigUint::from_str_radix("123456789ABCDEF", 16).unwrap();
        let arr = biguint_to_u64_array(&original);

        // Convert back
        let mut reconstructed = BigUint::from(0u64);
        for (i, &limb) in arr.iter().enumerate() {
            reconstructed += BigUint::from(limb) << (64 * i);
        }

        assert_eq!(original, reconstructed);
    }

    #[test]
    fn test_compute_r2_is_deterministic() {
        let modulus = BigUint::from(17u64);
        let r2_1 = compute_r2_bigint(&modulus);
        let r2_2 = compute_r2_bigint(&modulus);

        assert_eq!(r2_1, r2_2, "R2 computation should be deterministic");
    }

    #[test]
    fn test_compute_n_prime_is_deterministic() {
        let modulus = BigUint::from(17u64);
        let n_prime_1 = compute_n_prime_bigint(&modulus);
        let n_prime_2 = compute_n_prime_bigint(&modulus);

        assert_eq!(
            n_prime_1, n_prime_2,
            "N' computation should be deterministic"
        );
    }
}
