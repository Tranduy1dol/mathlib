# Mathematical Theory & Concepts in lumen-math

This document explains the mathematical concepts, algorithms, and theory implemented in the lumen-math library.

---

## Table of Contents

1. [Big Integer Arithmetic](#big-integer-arithmetic)
2. [Finite Field Arithmetic](#finite-field-arithmetic)
3. [Montgomery Multiplication](#montgomery-multiplication)
4. [Polynomial Operations](#polynomial-operations)
5. [Number Theoretic Transform (NTT)](#number-theoretic-transform-ntt)
6. [Negacyclic NTT](#negacyclic-ntt)
7. [Number Theory Algorithms](#number-theory-algorithms)
8. [Cryptographic Applications](#cryptographic-applications)

---

## Big Integer Arithmetic

### U1024 - 1024-bit Unsigned Integers

The `U1024` type represents unsigned integers up to $2^{1024} - 1$, stored as 16 × 64-bit limbs in little-endian order.

**Representation:**

$$
\texttt{U1024}([\text{limb}_0, \text{limb}_1, \ldots, \text{limb}_{15}])
$$

$$
\text{value} = \text{limb}_0 + \text{limb}_1 \cdot 2^{64} + \text{limb}_2 \cdot 2^{128} + \cdots + \text{limb}_{15} \cdot 2^{960}
$$

**Operations implemented:**
- Addition/Subtraction with carry/borrow propagation
- Multiplication using schoolbook algorithm: $O(n^2)$
- Division using binary long division
- Left/Right bit shifts
- Modular exponentiation (square-and-multiply)

### I1024 - 1024-bit Signed Integers

The `I1024` type uses magnitude + sign representation for signed arithmetic.

---

## Finite Field Arithmetic

### Prime Fields $\mathbb{F}_p$

A prime field $\mathbb{F}_p$ is the set of integers $\{0, 1, 2, \ldots, p-1\}$ with arithmetic modulo prime $p$.

**Properties:**
- Closure: $a + b, a \times b \in \mathbb{F}_p$
- Inverse exists for all non-zero elements: $a^{-1}$ where $a \cdot a^{-1} \equiv 1 \pmod{p}$
- Computed via Fermat's Little Theorem: $a^{-1} = a^{p-2} \mod p$

### FieldElement\<C\>

Generic field element parameterized by a `FieldConfig` trait that defines:
- `MODULUS`: The prime $p$
- `R2`: $R^2 \mod p$ (for Montgomery form)
- `N_PRIME`: Montgomery constant $N'$
- `ROOT_OF_UNITY`: Primitive $N$-th root of unity

---

## Montgomery Multiplication

Montgomery multiplication enables fast modular multiplication without division.

### Key Idea

Instead of computing $a \cdot b \mod p$ directly, work in "Montgomery form":
- Convert: $\bar{a} = a \cdot R \mod p$ (where $R = 2^{1024}$)
- Multiply: $\bar{a} \cdot \bar{b} \cdot R^{-1} \mod p = (a \cdot b \cdot R) \mod p$
- Convert back: $\text{result} \cdot R^{-1} \mod p$

### Montgomery Reduction (REDC)

Given $T = a \cdot b$ (2048-bit product), compute $T \cdot R^{-1} \mod p$:

$$
\begin{aligned}
m &= (T \mod R) \cdot N' \mod R \\
t &= \frac{T + m \cdot N}{R}
\end{aligned}
$$

$$
\text{return } 
\begin{cases} 
t - N & \text{if } t \geq N \\ 
t & \text{otherwise} 
\end{cases}
$$

where $N' \cdot N \equiv -1 \pmod{R}$

### Constants

- $R = 2^{1024}$ (implicit, power of 2 for efficiency)
- $R^2 = R^2 \mod p$ (for converting to Montgomery form)
- $N' = -p^{-1} \mod R$ (Montgomery constant)

---

## Polynomial Operations

### Univariate Polynomials

A polynomial over $\mathbb{F}_p$:

$$
p(x) = c_0 + c_1 x + c_2 x^2 + \cdots + c_n x^n
$$

**Implemented operations:**
- Arithmetic: $+, -, \times, \div$ with remainder
- Evaluation using **Horner's Method**: $O(n)$
- Derivative: $p'(x) = c_1 + 2c_2 x + 3c_3 x^2 + \cdots$
- **Lagrange Interpolation**: Given $n$ points, find unique polynomial of degree $< n$

### Horner's Method

Efficient evaluation:

$$
p(x) = c_0 + x(c_1 + x(c_2 + x(\cdots)))
$$

```
result = c_n
for i from n-1 down to 0:
    result = result · x + c_i
```

Time: $O(n)$ multiplications instead of $O(n^2)$ for naive method.

### Lagrange Interpolation

Given points $(x_0, y_0), \ldots, (x_{n-1}, y_{n-1})$, the interpolating polynomial is:

$$
p(x) = \sum_{i=0}^{n-1} y_i \cdot L_i(x)
$$

where the Lagrange basis polynomials are:

$$
L_i(x) = \prod_{j \neq i} \frac{x - x_j}{x_i - x_j}
$$

### Multivariate Polynomials

Sparse representation using `BTreeMap<Exponent, Coefficient>` where exponent is a vector $[e_0, e_1, \ldots, e_k]$ representing:

$$
x_0^{e_0} \cdot x_1^{e_1} \cdots x_k^{e_k}
$$

---

## Number Theoretic Transform (NTT)

The NTT is the finite field analog of the FFT, enabling $O(n \log n)$ polynomial multiplication.

### Cyclic NTT

Operates over the ring $\mathbb{Z}_q[X]/(X^N - 1)$.

**Forward NTT:**

Given coefficients $[c_0, c_1, \ldots, c_{n-1}]$, compute evaluations at powers of $\omega$:

$$
\hat{c}_k = \sum_{j=0}^{n-1} c_j \cdot \omega^{jk} \mod q
$$

where $\omega$ is a primitive $N$-th root of unity ($\omega^N \equiv 1 \pmod{q}$).

**Inverse NTT:**

$$
c_j = N^{-1} \cdot \sum_{k=0}^{n-1} \hat{c}_k \cdot \omega^{-jk} \mod q
$$

### Cooley-Tukey Algorithm

In-place butterfly computation with bit-reversal permutation:

```
for each layer len = 2, 4, 8, ..., N:
    ω_len = ω^(N/len)      // twiddle factor
    for each group:
        w = 1
        for j in half_len:
            u = coeffs[j]
            v = coeffs[j + half_len] · w
            coeffs[j] = u + v
            coeffs[j + half_len] = u - v
            w = w · ω_len
```

### Requirements

1. $N$ must be a power of 2
2. $q$ must be prime with $q \equiv 1 \pmod{N}$
3. $\omega$ must be a primitive $N$-th root of unity: $\omega^N \equiv 1$, $\omega^{N/2} \not\equiv 1$

---

## Negacyclic NTT

For lattice-based cryptography (Kyber, Dilithium), we need polynomial multiplication in the ring:

$$
R_q = \mathbb{Z}_q[X]/(X^N + 1)
$$

This means $X^N \equiv -1$, so coefficients "wrap around" with negation.

### Primitive 2N-th Root of Unity

Requires $\psi$ such that:

$$
\psi^N \equiv -1 \pmod{q} \quad \text{and} \quad \psi^{2N} \equiv 1 \pmod{q}
$$

### Algorithm (Twist Method)

**Forward Negacyclic NTT:**

1. Pre-multiply: $c'_i = c_i \cdot \psi^i$
2. Apply standard NTT with $\omega = \psi^2$

**Inverse Negacyclic NTT:**

1. Apply inverse NTT
2. Post-multiply: $c_i = c'_i \cdot \psi^{-i} \cdot N^{-1}$

### Field Configurations

| Scheme | $q$ | $N$ | $\psi$ (2N-th root) | $\omega = \psi^2$ |
|--------|-----|-----|---------------------|-------------------|
| **Kyber** | 3329 | 256 | 17 | 289 |
| **Dilithium** | 8380417 | 256 | 1753 | 3073009 |

### Ring Elements

The `RingElement<C>` type encapsulates polynomials in the ring $R_q$ with lazy state management:

**State Representation:**
- **Coefficient form**: $[c_0, c_1, \ldots, c_{N-1}]$ — natural representation
- **NTT form**: $[\hat{c}_0, \hat{c}_1, \ldots, \hat{c}_{N-1}]$ — transformed for multiplication

**Lazy Conversion:**
- Addition/Subtraction: Operates in coefficient form (auto-converts if needed)
- Multiplication: Operates in NTT form (pointwise multiplication is $O(N)$)
- Negation: Works in either form (coefficient-wise negation)

**Efficiency:**
- Shared `NttContext<C>` via `Arc` avoids recomputing twiddle factors
- State tracking prevents redundant conversions

---

## Number Theory Algorithms

### Extended Euclidean Algorithm (ExtGCD)

Computes $\gcd(a, b)$ and Bézout coefficients $x, y$ such that:

$$
ax + by = \gcd(a, b)
$$

```python
def extended_gcd(a, b):
    if b == 0:
        return (a, 1, 0)
    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1
    
    while r != 0:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
        old_t, t = t, old_t - q * t
    
    return (old_r, old_s, old_t)
```

### Modular Inverse

$a^{-1} \mod m$ exists if and only if $\gcd(a, m) = 1$.

Using ExtGCD: if $ax + my = 1$, then $a^{-1} \equiv x \pmod{m}$.

### Chinese Remainder Theorem (CRT)

Given a system of congruences:

$$
\begin{aligned}
x &\equiv a_1 \pmod{n_1} \\
x &\equiv a_2 \pmod{n_2} \\
&\vdots \\
x &\equiv a_k \pmod{n_k}
\end{aligned}
$$

If all $n_i$ are pairwise coprime, there exists a unique solution modulo $N = n_1 \cdot n_2 \cdots n_k$:

$$
x = \sum_{i=1}^{k} a_i \cdot N_i \cdot y_i \pmod{N}
$$

where $N_i = N/n_i$ and $y_i = N_i^{-1} \mod n_i$.

---

## Cryptographic Applications

### Zero-Knowledge Proofs

- **Polynomial commitments**: Commit to polynomials, prove evaluations
- **Lagrange interpolation**: Reconstruct polynomials from point evaluations
- **FFT/NTT**: Fast polynomial multiplication in proof systems (STARKs, Plonk)

### Lattice-Based Cryptography

The negacyclic NTT enables efficient operations in:

- **Kyber** (ML-KEM): Key encapsulation mechanism
- **Dilithium** (ML-DSA): Digital signature algorithm

Both operate over $R_q = \mathbb{Z}_q[X]/(X^N + 1)$ where polynomial multiplication is the core operation.

### Big Integer Cryptography

- **RSA**: Modular exponentiation of 2048+ bit integers
- **Elliptic Curves**: Large prime field arithmetic
- **Paillier**: Homomorphic encryption with large composites

---

## References

1. **Montgomery Multiplication**: P. Montgomery, "Modular Multiplication Without Trial Division" (1985)
2. **Cooley-Tukey FFT**: J. Cooley & J. Tukey, "An Algorithm for the Machine Calculation of Complex Fourier Series" (1965)
3. **NTT**: A. Agarwal & J. Cooley, "New algorithms for digital convolution" (1977)
4. **Kyber/Dilithium**: NIST Post-Quantum Cryptography Standardization
5. **Chinese Remainder Theorem**: Classical number theory result (Sun Tzu, ~3rd century CE)
