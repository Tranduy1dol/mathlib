use lumen_math::{I1024, U1024, i1024};

#[test]
fn test_i1024_construction_macros() {
    let a = i1024!(100u64);
    assert_eq!(a.magnitude(), U1024::from_u64(100));
    assert!(a.is_positive());

    let b = i1024!(-100);
    assert_eq!(b.magnitude(), U1024::from_u64(100));
    assert!(b.is_negative());

    let c = i1024!(U1024::from_u64(123));
    assert_eq!(c.magnitude(), U1024::from_u64(123));
    assert!(c.is_positive());
}

#[test]
fn test_i1024_arithmetic_basic() {
    let a = i1024!(10u64);
    let b = i1024!(-20);

    // Add
    assert_eq!(a + b, i1024!(-10));
    assert_eq!(b + a, i1024!(-10));
    assert_eq!(a + a, i1024!(20u64));
    assert_eq!(b + b, i1024!(-40));

    // Sub
    assert_eq!(a - b, i1024!(30u64));
    assert_eq!(b - a, i1024!(-30));

    // Mul
    assert_eq!(a * b, i1024!(-200));
    assert_eq!(b * a, i1024!(-200));
    assert_eq!(b * b, i1024!(400u64));
}

#[test]
fn test_i1024_zero_behavior() {
    let z = I1024::ZERO;
    let neg_z = -z;

    assert!(z.is_positive());
    assert!(!z.is_negative());
    assert!(z.is_zero());

    assert!(neg_z.is_positive()); // Zero is always positive logic
    assert!(neg_z.is_zero());
    assert_eq!(z, neg_z);

    let a = i1024!(10u64);
    assert_eq!(a + z, a);
    assert_eq!(a * z, z);
    assert_eq!(z - a, -a);
}

#[test]
fn test_i1024_display() {
    let pos = i1024!(12345u64);
    let neg = i1024!(-12345);

    // U1024 displays as hex with full padding
    // 12345 = 0x3039
    assert!(format!("{}", pos).ends_with("3039"));
    assert!(format!("{}", neg).contains("-"));
    assert!(format!("{}", neg).ends_with("3039"));
}
