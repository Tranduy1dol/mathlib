use mathlib::{DensePolynomial, fp};

fn main() {
    // Create some example polynomials

    // P(x) = 3x^2 + 2x + 1
    let p1 = DensePolynomial::new(vec![fp!(1u64), fp!(2u64), fp!(3u64)]);
    println!("P₁(x) = {}", p1);
    println!("Debug: {:?}\n", p1);

    // P(x) = 5x^4 + 3x^2 + 7
    let p2 = DensePolynomial::new(vec![fp!(7u64), fp!(0u64), fp!(3u64), fp!(0u64), fp!(5u64)]);
    println!("P₂(x) = {}", p2);

    // P(x) = x^3 - notice coefficient 1 is omitted for cleaner display
    let p3 = DensePolynomial::new(vec![fp!(0u64), fp!(0u64), fp!(0u64), fp!(1u64)]);
    println!("P₃(x) = {}", p3);

    // P(x) = x
    let p4 = DensePolynomial::new(vec![fp!(0u64), fp!(1u64)]);
    println!("P₄(x) = {}", p4);

    // P(x) = 42 (constant polynomial)
    let p5 = DensePolynomial::new(vec![fp!(42u64)]);
    println!("P₅(x) = {}", p5);

    // Multiplication example
    let product = p4.clone() * p5.clone();
    println!("\nP₄ × P₅ = ({}) × ({}) = {}", p4, p5, product);
}
