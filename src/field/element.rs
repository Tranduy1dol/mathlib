use std::fmt;
use std::marker::PhantomData;
use std::ops::{Add, Mul, Neg, Sub};

use crate::{BigInt, FieldConfig, U1024};

/// Macro to create a FieldElement from different sources.
///
/// Use `fp!(val)` for the default configuration, or `fp!(val, Config)` for a specific configuration.
///
/// # Examples
///
/// ```
/// use mathlib::{fp, u1024};
/// use mathlib::field::config::DefaultFieldConfig;
///
/// // Uses DefaultFieldConfig
/// let a = fp!("0x1234");
///
/// // Explicit config
/// let b = fp!("0x1234", DefaultFieldConfig);
/// ```
#[macro_export]
macro_rules! fp {
    // Default config
    ($val:expr) => {
        fp!($val, $crate::field::config::DefaultFieldConfig)
    };
    // Explicit config
    ($val:expr, $config:ty) => {{
        #[allow(unused_imports)]
        {
            // Helper trait to convert to FieldElement
            trait ToFieldElement {
                fn to_field_element(self) -> $crate::field::element::FieldElement<$config>;
            }

            impl ToFieldElement for &str {
                fn to_field_element(self) -> $crate::field::element::FieldElement<$config> {
                    $crate::field::element::FieldElement::<$config>::new($crate::U1024::from_hex(
                        self,
                    ))
                }
            }

            impl ToFieldElement for u8 {
                fn to_field_element(self) -> $crate::field::element::FieldElement<$config> {
                    $crate::field::element::FieldElement::<$config>::new($crate::U1024::from_u8(
                        self,
                    ))
                }
            }

            impl ToFieldElement for u16 {
                fn to_field_element(self) -> $crate::field::element::FieldElement<$config> {
                    $crate::field::element::FieldElement::<$config>::new($crate::U1024::from_u16(
                        self,
                    ))
                }
            }

            impl ToFieldElement for u32 {
                fn to_field_element(self) -> $crate::field::element::FieldElement<$config> {
                    $crate::field::element::FieldElement::<$config>::new($crate::U1024::from_u32(
                        self,
                    ))
                }
            }

            impl ToFieldElement for u64 {
                fn to_field_element(self) -> $crate::field::element::FieldElement<$config> {
                    $crate::field::element::FieldElement::<$config>::new($crate::U1024::from_u64(
                        self,
                    ))
                }
            }

            impl ToFieldElement for u128 {
                fn to_field_element(self) -> $crate::field::element::FieldElement<$config> {
                    $crate::field::element::FieldElement::<$config>::new($crate::U1024::from_u128(
                        self,
                    ))
                }
            }

            impl ToFieldElement for $crate::U1024 {
                fn to_field_element(self) -> $crate::field::element::FieldElement<$config> {
                    $crate::field::element::FieldElement::<$config>::new(self)
                }
            }

            ToFieldElement::to_field_element($val)
        }
    }};
}

#[derive(Clone, Copy)]
pub struct FieldElement<C: FieldConfig> {
    pub value: U1024,
    _marker: PhantomData<C>,
}

impl<C: FieldConfig> FieldElement<C> {
    /// Constructs a FieldElement by converting a standard integer into a Montgomery form.
    ///
    /// This function is `const`, enabling compile-time creation of field elements.
    pub const fn new(value: U1024) -> Self {
        let (lo, hi) = value.const_mul(&C::R2);
        let mont_value = Self::const_reduce(&lo, &hi);

        Self {
            value: mont_value,
            _marker: PhantomData,
        }
    }

    /// Creates a FieldElement from an existing value already in Montgomery representation.
    pub const fn from_montgomery(value: U1024) -> Self {
        Self {
            value,
            _marker: PhantomData,
        }
    }

    /// Constructs the additive identity (zero).
    pub const fn zero() -> Self {
        Self {
            value: U1024::ZERO,
            _marker: PhantomData,
        }
    }

    /// Constructs the multiplicative identity (one).
    pub const fn one() -> Self {
        Self::new(Self::const_one_u1024())
    }

    // Const helper for one()
    const fn const_one_u1024() -> U1024 {
        let mut limbs = [0u64; 16];
        limbs[0] = 1;
        U1024(limbs)
    }

    /// Convert this element from Montgomery form into its canonical U1024 representation.
    pub fn to_u1024(&self) -> U1024 {
        C::to_montgomery_context().reduce(&self.value, &U1024::ZERO)
    }

    /// Internal const reduction function logic.
    const fn const_reduce(lo: &U1024, hi: &U1024) -> U1024 {
        // m = (lo * n_prime) mod R (take lower 1024 bits)
        let (m_lo, _) = lo.const_mul(&C::N_PRIME);
        let m = m_lo; // This is 'm'

        // mn = m * modulus
        let (mn_lo, mn_hi) = m.const_mul(&C::MODULUS);

        // t = (lo + mn) / R + hi
        // (lo + mn_lo) will automatically be 0 mod R, effectively just carries.
        // We only care about carry_lo and adding to hi.

        // (_, carry_lo) = lo.carrying_add(mn_lo)
        let (_, carry_lo) = lo.const_add(&mn_lo);

        // (res_hi, carry_hi) = hi.carrying_add(mn_hi)
        let (res_hi, carry_hi) = hi.const_add(&mn_hi);

        // Add carry_lo to res_hi
        let (t, carry_final) = if carry_lo {
            res_hi.const_add(&Self::const_one_u1024())
        } else {
            (res_hi, false)
        };

        // If carry_hi or carry_final, result > P, so subtract P.
        if carry_hi || carry_final {
            let (sub_res, _) = t.const_sub(&C::MODULUS);
            return sub_res;
        }

        // Else check if t >= P
        // const_sub returns borrow if t < P. If no borrow, t >= P, so we return diff.
        // If borrow, t < P, so we return t.

        let (sub_res, borrow) = t.const_sub(&C::MODULUS);
        if !borrow { sub_res } else { t }
    }

    /// Computes `self` raised to the power of `exp` using square-and-multiply.
    pub fn pow(&self, exp: U1024) -> Self {
        let mut res = Self::one(); // runtime version of one? Const one!
        let mut base = *self;

        for i in 0..16 {
            let mut limb = exp.0[i];
            for _ in 0..64 {
                if (limb & 1) == 1 {
                    res = res * base;
                }
                base = base * base;
                limb >>= 1;
            }
        }
        res
    }

    pub fn inv(&self) -> Self {
        let two = U1024::from_u64(2);
        let (p_minus_2, _) = C::MODULUS.borrowing_sub(&two);
        self.pow(p_minus_2)
    }

    pub fn is_zero(&self) -> bool {
        self.value == U1024::ZERO
    }

    pub fn double(&self) -> Self {
        *self + *self
    }

    pub fn square(&self) -> Self {
        *self * *self
    }
}


// Trait Implementations

impl<C: FieldConfig> Add for FieldElement<C> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        let (sum, carry) = self.value.carrying_add(&rhs.value);
        let (sub_res, borrow) = sum.borrowing_sub(&C::MODULUS);
        let use_sub = carry || !borrow;

        Self {
            value: U1024::conditional_select(&sub_res, &sum, use_sub),
            _marker: PhantomData,
        }
    }
}

impl<C: FieldConfig> Sub for FieldElement<C> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        let (diff, borrow) = self.value.borrowing_sub(&rhs.value);
        let (corr, _) = diff.carrying_add(&C::MODULUS);

        Self {
            value: U1024::conditional_select(&corr, &diff, borrow),
            _marker: PhantomData,
        }
    }
}

impl<C: FieldConfig> Mul for FieldElement<C> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        let (lo, hi) = self.value.full_mul(&rhs.value);
        // Delegate to runtime reduce for performance (uses GMP/AVX if available)
        let res = C::to_montgomery_context().reduce(&lo, &hi);

        Self {
            value: res,
            _marker: PhantomData,
        }
    }
}

impl<C: FieldConfig> Neg for FieldElement<C> {
    type Output = Self;
    fn neg(self) -> Self {
        if self.is_zero() {
            self
        } else {
            let (value, _) = C::MODULUS.borrowing_sub(&self.value);
            Self {
                value,
                _marker: PhantomData,
            }
        }
    }
}

impl<C: FieldConfig> fmt::Debug for FieldElement<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let raw = self.to_u1024();
        write!(f, "FieldElement({:?})", raw)
    }
}

impl<C: FieldConfig> PartialEq for FieldElement<C> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl<C: FieldConfig> Eq for FieldElement<C> {}
