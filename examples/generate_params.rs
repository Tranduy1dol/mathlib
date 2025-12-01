use num_bigint::{BigUint, RandBigInt};
use num_integer::Integer;
use num_traits::One;

fn main() {
    println!("🔍 Searching for 1024-bit NTT-friendly prime...");
    let n_power = 32;
    let two_pow_32 = BigUint::one() << n_power;

    let mut rng = rand::thread_rng();

    loop {
        let mut k = rng.gen_biguint(992);
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
    let mut rng = rand::thread_rng();
    let one = BigUint::one();
    let two_pow_n_minus_1 = BigUint::one() << (n - 1);

    loop {
        let g = rng.gen_biguint_range(&BigUint::from(2u32), p);

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

    let mut rng = rand::thread_rng();
    'witness: for _ in 0..k {
        let a = rng.gen_biguint_range(&two, &n_minus_1);

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
