use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::One;
use rand::Rng;

fn main() {
    println!("🔍 Searching for 1024-bit NTT-friendly prime...");
    let n_power = 32;
    let two_pow_32 = BigUint::one() << n_power;

    let mut rng = rand::rng();

    loop {
        let mut k = gen_biguint(&mut rng, 992);
        k |= BigUint::one() << 991;
        k |= BigUint::one();
        if k.is_even() {
            continue;
        }

        let p: BigUint = &k * &two_pow_32 + BigUint::one();

        if p.bits() == 1024 && is_prob_prime(&p, 20) {
            println!("✅ FOUND PRIME P!");
            println!("P (Hex) = 0x{:X}", p);

            let root = find_primitive_root(&p, &k, n_power);
            println!("✅ FOUND ROOT OF UNITY w (order 2^32)!");
            println!("w (Hex) = 0x{:X}", root);
            break;
        }
    }
}

fn find_primitive_root(p: &BigUint, k: &BigUint, n: u32) -> BigUint {
    let mut rng = rand::rng();
    let one = BigUint::one();
    let two_pow_n_minus_1 = BigUint::one() << (n - 1);

    loop {
        let g = gen_biguint_range(&mut rng, &BigUint::from(2u32), p);

        let w = g.modpow(k, p);

        let check = w.modpow(&two_pow_n_minus_1, p);

        if check != one && w != one {
            return w;
        }
    }
}

fn is_prob_prime(n: &BigUint, k: usize) -> bool {
    if n <= &BigUint::from(1u32) {
        return false;
    }
    if n <= &BigUint::from(3u32) {
        return true;
    }
    if n.is_even() {
        return false;
    }

    let one = BigUint::one();
    let two = BigUint::from(2u32);
    let n_minus_1 = n - &one;

    let mut d = n_minus_1.clone();
    let mut r = 0;
    while d.is_even() {
        d >>= 1;
        r += 1;
    }

    let mut rng = rand::rng();
    'witness: for _ in 0..k {
        let a = gen_biguint_range(&mut rng, &two, &n_minus_1);

        let mut x = a.modpow(&d, n);

        if x == one || x == n_minus_1 {
            continue;
        }

        for _ in 0..r - 1 {
            x = x.modpow(&two, n);
            if x == n_minus_1 {
                continue 'witness;
            }
        }
        return false;
    }
    true
}

/// Generate a random BigUint with the specified number of bits
fn gen_biguint<R: Rng>(rng: &mut R, bits: usize) -> BigUint {
    let bytes_needed = (bits + 7).div_ceil(8);
    let mut bytes = vec![0u8; bytes_needed];
    rng.fill(&mut bytes[..]);

    // Mask the top byte if bits is not a multiple of 8
    let extra_bits = bits % 8;
    if extra_bits != 0 {
        bytes[bytes_needed - 1] &= (1u8 << extra_bits) - 1;
    }

    BigUint::from_bytes_le(&bytes)
}

/// Generate a random BigUint in the range [low, high)
fn gen_biguint_range<R: Rng>(rng: &mut R, low: &BigUint, high: &BigUint) -> BigUint {
    use num_traits::Zero;

    let range = high - low;
    if range.is_zero() {
        return low.clone();
    }

    let bits = range.bits() as usize;
    loop {
        let candidate = gen_biguint(rng, bits);
        if candidate < range {
            return low + candidate;
        }
    }
}
