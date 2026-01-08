use lumen_math::{DefaultFieldConfig, Digest, FieldElement, U1024};

#[test]
fn test_digest_u1024_deterministic() {
    let input = b"test message";
    let hash1 = U1024::from_hash(input);
    let hash2 = U1024::from_hash(input);

    assert_eq!(hash1, hash2, "Hashing must be deterministic");
    assert_ne!(
        hash1,
        U1024::ZERO,
        "Hash shouldn't be zero (probability is low)"
    );
}

#[test]
fn test_digest_u1024_domain_separation() {
    let input = b"same message";
    let domain1 = b"app_v1";
    let domain2 = b"app_v2";

    let hash1 = U1024::from_hash_with_domain(domain1, input);
    let hash2 = U1024::from_hash_with_domain(domain2, input);

    assert_ne!(
        hash1, hash2,
        "Different domains must produce different hashes"
    );
}

#[test]
fn test_digest_field_element() {
    // Tests that FieldElement implements Digest via U1024
    let input = b"field element input";
    let fe: FieldElement<DefaultFieldConfig> = FieldElement::from_hash(input);

    // Manual construction to verify
    let u_hash = U1024::from_hash(input);
    let fe_manual = FieldElement::<DefaultFieldConfig>::new(u_hash);

    assert_eq!(fe, fe_manual);
}

#[test]
fn test_digest_field_element_domain() {
    let input = b"field data";
    let domain = b"my_domain";

    // Test FieldElement::from_hash_with_domain
    let fe: FieldElement<DefaultFieldConfig> = FieldElement::from_hash_with_domain(domain, input);

    // Verify it matches U1024::from_hash_with_domain + valid reduction
    let u_val = U1024::from_hash_with_domain(domain, input);
    let fe_manual = FieldElement::<DefaultFieldConfig>::new(u_val);

    assert_eq!(fe, fe_manual);

    // Verify different domains produce different field elements
    let fe2: FieldElement<DefaultFieldConfig> = FieldElement::from_hash_with_domain(b"diff", input);
    assert_ne!(fe, fe2);
}

#[test]
fn test_digest_vectors() {
    let input = b"mathlib";
    let hash = U1024::from_hash(input);
    let hash2 = U1024::from_hash(input);
    assert_eq!(hash, hash2);
}
