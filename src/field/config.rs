use std::fmt::Debug;

use crate::{MontgomeryContext, U1024};

/// Configuration trait for defining field parameters at the type level.
///
/// This trait allows `FieldElement` to use generic parameters `C` to access
/// field constants like the modulus, R^2, and root of unity at compile time,
/// enabling `const` constructors and efficient arithmetic without runtime references.
pub trait FieldConfig:
    'static + Copy + Clone + Debug + Default + PartialEq + Eq + Send + Sync
{
    /// The prime modulus P.
    const MODULUS: U1024;

    /// The number of bits in the modulus.
    const MODULUS_BITS: u32;

    /// R^2 mod P, used for Montgomery multiplication.
    const R2: U1024;

    /// The Montgomery constant n' satisfying P * n' ≡ -1 (mod 2^1024).
    const N_PRIME: U1024;

    /// A primitive root of unity in the field.
    const ROOT_OF_UNITY: U1024;

    /// Primitive 2Nth root of unity (ψ) for Negacyclic NTT.
    /// Must satisfy ψ^N ≡ -1 (mod MODULUS).
    /// Defaults to ROOT_OF_UNITY for backward compatibility.
    const PRIMITIVE_2NTH_ROOT: U1024 = Self::ROOT_OF_UNITY;

    /// The polynomial ring degree N for NTT operations.
    /// Defaults to 256 for Kyber/Dilithium compatibility.
    const NTT_DEGREE: usize = 256;

    /// Helper to convert the type-level config into a runtime `MontgomeryContext`.
    fn to_montgomery_context() -> MontgomeryContext {
        MontgomeryContext {
            modulus: Self::MODULUS,
            r2: Self::R2,
            n_prime: Self::N_PRIME,
            root_of_unity: Self::ROOT_OF_UNITY,
        }
    }
}

/// Default field configuration using the standard parameters.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct DefaultFieldConfig;

impl FieldConfig for DefaultFieldConfig {
    const MODULUS: U1024 = U1024([
        8283057860145840129,
        3288163704127842800,
        3538805720522839775,
        13656773141428525553,
        14668624012991748934,
        15071484231171862341,
        14557163493085018070,
        8760060930287064779,
        18314798345233646567,
        10372120154783610375,
        11013173786378992407,
        2346218445531158615,
        14951578807925983019,
        11781538484505028703,
        5520364913440643725,
        14875008987934475874,
    ]);

    const MODULUS_BITS: u32 = 1024; // Implicitly 1024 for U1024

    const R2: U1024 = U1024([
        13939754187685836846,
        1381783175514922841,
        10510526148727125376,
        6517033096596299871,
        6450033995612272586,
        14921398717934335171,
        3907414530314885341,
        11312112684330026423,
        2312050913270528722,
        3445478028676178292,
        6613985790582183390,
        3381746159472020493,
        13662159530254212867,
        18053211607220481434,
        9633908589134576428,
        9857584817118838755,
    ]);

    const N_PRIME: U1024 = U1024([
        8283057860145840127,
        11236579508417976679,
        2939118415303464292,
        2490076508057013032,
        15361143824052074994,
        10701702357461113392,
        2712387106149303063,
        17503520260228677384,
        359269105795793623,
        6710084597776894878,
        7831247527261164119,
        525591964300195233,
        13122043338015330400,
        5103479632631951838,
        6021408692067195273,
        12541830714242010488,
    ]);

    const ROOT_OF_UNITY: U1024 = U1024([
        10204254570577251382,
        6144292756122420043,
        7304950242222435100,
        11712418833229072878,
        675023548738942677,
        2247951337588327474,
        13008887574266358693,
        12834753379748368629,
        15604002773547013110,
        5095755077795343082,
        12075133554490433169,
        1627954023658407127,
        9084262066193491870,
        11264389924692972233,
        5206305381954388724,
        2112739729668803901,
    ]);
}
