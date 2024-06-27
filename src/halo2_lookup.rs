use std::collections::BTreeMap;
use std::ops::Mul;

use ark_ec::pairing::Pairing;
use ark_poly::{univariate::{DenseOrSparsePolynomial, DensePolynomial}, DenseUVPolynomial, EvaluationDomain, Evaluations, Polynomial, Radix2EvaluationDomain};
use ark_poly_commit::kzg10::{Commitment, Powers, VerifierKey, KZG10};
use ark_std::{iterable::Iterable, rand::RngCore, Zero, One};

use crate::{permutation_check, utils::{batch_check, batch_open, construct_accumulator_for_prod_check, BatchCheckProof, Transcript}};

/// the lookup argument in halo2
/// [unoptimized] using two permutation checks
pub fn prove<E: Pairing, R: RngCore>(
    powers: &Powers<E>,
    a_evals: &Vec<u64>,
    s_evals: &Vec<u64>,
    domain: Radix2EvaluationDomain<E:: ScalarField>,
    rng: &mut R,
) -> Vec<BatchCheckProof<E>> {
    let (a_prime_evals, s_prime_evals) = sort(a_evals, s_evals);
    let a_evals: Vec<_> = a_evals.iter()
        .map(| eval | {
            E::ScalarField::from(*eval)
        })
        .collect();
    let s_evals: Vec<_> = s_evals.iter()
        .map(| eval | {
            E::ScalarField::from(*eval)
        })
        .collect();
    let a_prime_evals: Vec<_> = a_prime_evals.iter()
        .map(| eval | {
            E::ScalarField::from(*eval)
        })
        .collect();
    let s_prime_evals: Vec<_> = s_prime_evals.iter()
        .map(| eval | {
            E::ScalarField::from(*eval)
        })
        .collect();
    let mut a_prime_shifted_evals = a_prime_evals.clone();
    a_prime_shifted_evals.rotate_right(1);

    // A'(X)
    let a_prime = Evaluations::from_vec_and_domain(a_prime_evals.clone(), domain).interpolate();
    // S'(X)
    let s_prime = Evaluations::from_vec_and_domain(s_prime_evals.clone(), domain).interpolate();
    // A'(X/w)
    let a_prime_shifed = Evaluations::from_vec_and_domain(a_prime_shifted_evals, domain).interpolate();

    // [A'(X) - A'(X/w)] * [A'(X) - S'(X)]
    let mut w1 = &a_prime - &a_prime_shifed;
    let a_minus_s_prime = &a_prime - &s_prime;
    w1 = &w1 * &a_minus_s_prime;

    let z = DenseOrSparsePolynomial::from(domain.vanishing_polynomial());
    let (q1, r) = DenseOrSparsePolynomial::from(w1).divide_with_q_and_r(&z).unwrap();
    assert!(r.is_zero());

    // L0(X) * [A'(X) - S'(X)]
    let x_minus_one = DenseOrSparsePolynomial::from(DensePolynomial::from_coefficients_vec(vec![-E::ScalarField::one(), E::ScalarField::one()]));
    let (l0, r) = z.divide_with_q_and_r(&x_minus_one).unwrap();
    assert!(r.is_zero());
    let w2 = &l0 * &a_minus_s_prime;
    let (q2, r) = DenseOrSparsePolynomial::from(w2).divide_with_q_and_r(&z).unwrap();
    assert!(r.is_zero());

    // commit to A'(X)
    let (cm_a_prime, mask_a_prime) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &a_prime, 
            Some(a_prime.degree()), 
            Some(rng)
        ).unwrap();

    // commit to S'(X)
    let (cm_s_prime, mask_s_prime) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &s_prime,
            Some(s_prime.degree()), 
            Some(rng)
        ).unwrap();

    // commit to Q1
    let (cm_q1, mask_q1) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &q1, 
            Some(q1.degree()), 
            Some(rng)
        ).unwrap();

    // commit to Q2
    let (cm_q2, mask_q2) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &q2, 
            Some(q2.degree()), 
            Some(rng)
        ).unwrap();

    // calculate the challenge, zeta
    let mut transcript = Transcript::new();
    transcript.append_affines::<E>(&vec![
        cm_a_prime.0, cm_s_prime.0, cm_q1.0, cm_q2.0,
    ]);
    let zeta = transcript.append_and_digest::<E>("zeta".to_string());

    // open the evaluations at zeta for A', S', Q1 and Q2
    let (h1, open_evals1, gamma1) = batch_open(
        powers, 
        &vec![&a_prime, &s_prime, &q1, &q2], 
        &vec![&mask_a_prime, &mask_s_prime, &mask_q1, &mask_q2], 
        zeta, 
        false, 
        rng
    );

    let omega = domain.element(1);

    // open the evaluation at zeta*omega for A'
    let (h2, open_evals2, gamma2) = batch_open(
        powers, 
        &vec![&a_prime], 
        &vec![&mask_a_prime], 
        zeta / omega, 
        false, 
        rng
    );

    let proof = BatchCheckProof {
        commitments: vec![
            vec![cm_a_prime, cm_s_prime, cm_q1, cm_q2],
            vec![cm_a_prime],
        ],
        witnesses: vec![h1, h2],
        points: vec![zeta, zeta / omega],
        open_evals: vec![open_evals1, open_evals2],
        gammas: vec![gamma1, gamma2],
    };

    // prove A' is the permutation of A
    let perm_proof1 = permutation_check::prove(powers, &a_evals, &a_prime_evals, domain, rng);
    // prove S' is the permutation of S
    let perm_proof2 = permutation_check::prove(powers, &s_evals, &s_prime_evals, domain, rng);

    vec![proof, perm_proof1, perm_proof2]
}

pub fn verify<E: Pairing, R: RngCore>(
    vk: &VerifierKey<E>,
    proofs: &Vec<BatchCheckProof<E>>,
    domain: Radix2EvaluationDomain<E::ScalarField>,
    rng: &mut R,
) {
    let proof = &proofs[0];

    let cm_a_prime = proof.commitments[0][0];
    let cm_s_prime = proof.commitments[0][1];
    let cm_q1 = proof.commitments[0][2];
    let cm_q2 = proof.commitments[0][3];

    // verify zeta is correct
    let mut transcript = Transcript::new();
    transcript.append_affines::<E>(&vec![
        cm_a_prime.0, cm_s_prime.0, cm_q1.0, cm_q2.0,
    ]);
    let zeta = transcript.append_and_digest::<E>("zeta".to_string());
    assert_eq!(zeta, proof.points[0]);

    // verify zeta*omega is correct
    let omega = domain.element(1);
    assert_eq!(zeta / omega, proof.points[1]);

    // read the evaluations of A'(zeta), S'(zeta), Q1(zeta), A'(zeta*omega)
    let a_prime_zeta = &proof.open_evals[0][0].into_plain_value().0;
    let s_prime_zeta = &proof.open_evals[0][1].into_plain_value().0;
    let q1_zeta = &proof.open_evals[0][2].into_plain_value().0;
    let a_prime_zeta_omega = &proof.open_evals[1][0].into_plain_value().0;

    // evaluate Z(X) at zeta
    let z = domain.vanishing_polynomial();
    let z_zeta = z.evaluate(&zeta);

    // verify [A'(X) - A'(X/w)] * [A'(X) - S'(X)] = Z(X) * Q1(X)
    let lhs = (*a_prime_zeta - a_prime_zeta_omega).mul(*a_prime_zeta - s_prime_zeta);
    let rhs = z_zeta.mul(q1_zeta);
    assert_eq!(lhs, rhs);

    let q2_zeta = &proof.open_evals[0][3].into_plain_value().0;

    // verify L0(X) * [A'(X) - S'(X)] = Z(X) * Q2(X)
    let x_minus_one = DenseOrSparsePolynomial::from(DensePolynomial::from_coefficients_vec(vec![-E::ScalarField::one(), E::ScalarField::one()]));
    let (l0, _) = DenseOrSparsePolynomial::from(z).divide_with_q_and_r(&x_minus_one).unwrap();
    let l0_zeta = l0.evaluate(&zeta);
    let lhs = l0_zeta.mul(*a_prime_zeta - s_prime_zeta);
    let rhs = z_zeta.mul(q2_zeta);
    assert_eq!(lhs, rhs);

    batch_check(vk, proof, rng);
    
    for i in 1..proofs.len() {
        let proof = &proofs[i];
        permutation_check::verify(vk, proof, domain, rng);
    }
}

/// the lookup argument in halo2
/// using one permutation check
pub fn prove_v2<E: Pairing, R: RngCore>(
    powers: &Powers<E>,
    a_evals: &Vec<u64>,
    s_evals: &Vec<u64>,
    domain: Radix2EvaluationDomain<E:: ScalarField>,
    rng: &mut R,
) -> BatchCheckProof<E> {
    let (a_prime_evals, s_prime_evals) = sort(a_evals, s_evals);
    let a_evals: Vec<_> = a_evals.iter()
        .map(| eval | {
            E::ScalarField::from(*eval)
        })
        .collect();
    let s_evals: Vec<_> = s_evals.iter()
        .map(| eval | {
            E::ScalarField::from(*eval)
        })
        .collect();
    let a_prime_evals: Vec<_> = a_prime_evals.iter()
        .map(| eval | {
            E::ScalarField::from(*eval)
        })
        .collect();
    let s_prime_evals: Vec<_> = s_prime_evals.iter()
        .map(| eval | {
            E::ScalarField::from(*eval)
        })
        .collect();

    // A(X)
    let a = Evaluations::from_vec_and_domain(a_evals.clone(), domain).interpolate();
    // S(X)
    let s = Evaluations::from_vec_and_domain(s_evals.clone(), domain).interpolate();
    // A'(X)
    let a_prime = Evaluations::from_vec_and_domain(a_prime_evals.clone(), domain).interpolate();
    // S'(X)
    let s_prime = Evaluations::from_vec_and_domain(s_prime_evals.clone(), domain).interpolate();
    // A'(X/w)
    let mut a_prime_shifted_evals = a_prime.clone().evaluate_over_domain(domain).evals.clone();
    a_prime_shifted_evals.rotate_right(1);
    let a_prime_shifed = Evaluations::from_vec_and_domain(a_prime_shifted_evals, domain).interpolate();

    // [A'(X) - A'(X/w)] * [A'(X) - S'(X)]
    let mut w1 = &a_prime - &a_prime_shifed;
    let a_minus_s_prime = &a_prime - &s_prime;
    w1 = &w1 * &a_minus_s_prime;

    let z = DenseOrSparsePolynomial::from(domain.vanishing_polynomial());
    let (q1, r) = DenseOrSparsePolynomial::from(w1).divide_with_q_and_r(&z).unwrap();
    assert!(r.is_zero());

    // L0(X) * [A'(X) - S'(X)]
    let x_minus_one = DenseOrSparsePolynomial::from(DensePolynomial::from_coefficients_vec(vec![-E::ScalarField::one(), E::ScalarField::one()]));
    let (l0, r) = z.divide_with_q_and_r(&x_minus_one).unwrap();
    assert!(r.is_zero());
    let w2 = &l0 * &a_minus_s_prime;
    let (q2, r) = DenseOrSparsePolynomial::from(w2).divide_with_q_and_r(&z).unwrap();
    assert!(r.is_zero());

    // commit to A(X)
    let (cm_a, mask_a) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &a, 
            Some(a.degree()), 
            Some(rng)
        ).unwrap();

    // commit to S(X)
    let (cm_s, mask_s) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &s,
            Some(s.degree()), 
            Some(rng)
        ).unwrap();

    // commit to A'(X)
    let (cm_a_prime, mask_a_prime) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &a_prime, 
            Some(a_prime.degree()), 
            Some(rng)
        ).unwrap();

    // commit to S'(X)
    let (cm_s_prime, mask_s_prime) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &s_prime,
            Some(s_prime.degree()), 
            Some(rng)
        ).unwrap();

    let (b, q3, q4) = prove_v2_permutation(&a, &s, &a_prime, &s_prime, &cm_a, &cm_s, &cm_a_prime, &cm_s_prime, domain);

    // commit to B
    let (cm_b, mask_b) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &b, 
            Some(b.degree()), 
            Some(rng)
        ).unwrap();

    // commit to Q1
    let (cm_q1, mask_q1) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &q1, 
            Some(q1.degree()), 
            Some(rng)
        ).unwrap();

    // commit to Q2
    let (cm_q2, mask_q2) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &q2, 
            Some(q2.degree()), 
            Some(rng)
        ).unwrap();

    // commit to Q3
    let (cm_q3, mask_q3) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &q3, 
            Some(q3.degree()), 
            Some(rng)
        ).unwrap();

    // commit to Q4
    let (cm_q4, mask_q4) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &q4, 
            Some(q4.degree()), 
            Some(rng)
        ).unwrap();

    // calculate the challenge, zeta
    let mut transcript = Transcript::new();
    transcript.append_affines::<E>(&vec![
        cm_a.0, cm_s.0, cm_b.0, cm_a_prime.0, cm_s_prime.0, cm_q1.0, cm_q2.0, cm_q3.0, cm_q4.0,
    ]);
    let zeta = transcript.append_and_digest::<E>("zeta".to_string());

    // open the evaluations at zeta for A, S, B, A', S', Q1, Q2, Q3, and Q4
    let (h1, open_evals1, gamma1) = batch_open(
        powers, 
        &vec![&a, &s, &b, &a_prime, &s_prime, &q1, &q2, &q3, &q4], 
        &vec![&mask_a, &mask_s, &mask_b, &mask_a_prime, &mask_s_prime, &mask_q1, &mask_q2, &mask_q3, &mask_q4], 
        zeta, 
        false, 
        rng
    );

    let omega = domain.element(1);

    // open the evaluation at zeta/omega for A'
    let (h2, open_evals2, gamma2) = batch_open(
        powers, 
        &vec![&a_prime], 
        &vec![&mask_a_prime], 
        zeta / omega, 
        false, 
        rng
    );

    // open the evaluation at zeta * omega for B
    let (h3, open_evals3, gamma3) = batch_open(
        powers, 
        &vec![&b], 
        &vec![&mask_b], 
        zeta * omega, 
        false, 
        rng
    );

    BatchCheckProof {
        commitments: vec![
            vec![cm_a, cm_s, cm_b, cm_a_prime, cm_s_prime, cm_q1, cm_q2, cm_q3, cm_q4],
            vec![cm_a_prime],
            vec![cm_b],
        ],
        witnesses: vec![h1, h2, h3],
        points: vec![zeta, zeta / omega, zeta * omega],
        open_evals: vec![
            open_evals1,
            open_evals2,
            open_evals3,
        ],
        gammas: vec![gamma1, gamma2, gamma3],
    }
}

pub fn verify_v2<E: Pairing, R: RngCore>(
    vk: &VerifierKey<E>,
    proof: &BatchCheckProof<E>,
    domain: Radix2EvaluationDomain<E::ScalarField>,
    rng: &mut R,
) {
    let cm_a = proof.commitments[0][0];
    let cm_s = proof.commitments[0][1];
    let cm_b = proof.commitments[0][2];
    let cm_a_prime = proof.commitments[0][3];
    let cm_s_prime = proof.commitments[0][4];
    let cm_q1 = proof.commitments[0][5];
    let cm_q2 = proof.commitments[0][6];
    let cm_q3 = proof.commitments[0][7];
    let cm_q4 = proof.commitments[0][8];

    // verify zeta is correct
    let mut transcript = Transcript::new();
    transcript.append_affines::<E>(&vec![
        cm_a.0, cm_s.0, cm_b.0, cm_a_prime.0, cm_s_prime.0, cm_q1.0, cm_q2.0, cm_q3.0, cm_q4.0,
    ]);
    let zeta = transcript.append_and_digest::<E>("zeta".to_string());
    assert_eq!(zeta, proof.points[0]);

    // verify zeta / omega is correct
    let omega = domain.element(1);
    assert_eq!(zeta / omega, proof.points[1]);

    // verify zeta * omega is correct
    assert_eq!(zeta * omega, proof.points[2]);

    // read the evaluations of A'(zeta), S'(zeta), Q1(zeta), A'(zeta*omega)
    let a_prime_zeta = &proof.open_evals[0][3].into_plain_value().0;
    let s_prime_zeta = &proof.open_evals[0][4].into_plain_value().0;
    let q1_zeta = &proof.open_evals[0][5].into_plain_value().0;
    let a_prime_zeta_omega = &proof.open_evals[1][0].into_plain_value().0;

    // evaluate Z(X) at zeta
    let z = domain.vanishing_polynomial();
    let z_zeta = z.evaluate(&zeta);

    // verify [A'(X) - A'(X/w)] * [A'(X) - S'(X)] = Z(X) * Q1(X)
    let lhs = (*a_prime_zeta - a_prime_zeta_omega).mul(*a_prime_zeta - s_prime_zeta);
    let rhs = z_zeta.mul(q1_zeta);
    assert_eq!(lhs, rhs);

    let q2_zeta = &proof.open_evals[0][6].into_plain_value().0;

    // verify L0(X) * [A'(X) - S'(X)] = Z(X) * Q2(X)
    let x_minus_one = DenseOrSparsePolynomial::from(DensePolynomial::from_coefficients_vec(vec![-E::ScalarField::one(), E::ScalarField::one()]));
    let (l0, _) = DenseOrSparsePolynomial::from(z).divide_with_q_and_r(&x_minus_one).unwrap();
    let l0_zeta = l0.evaluate(&zeta);
    let lhs = l0_zeta.mul(*a_prime_zeta - s_prime_zeta);
    let rhs = z_zeta.mul(q2_zeta);
    assert_eq!(lhs, rhs);

    let mut transcript = Transcript::new();
    transcript.append_affines::<E>(&vec![
        cm_a.0, cm_s.0, cm_a_prime.0, cm_s_prime.0,
    ]);
    let beta = transcript.append_and_digest::<E>("beta".to_string());
    let gamma = transcript.append_and_digest::<E>("gamma".to_string());

    let a_zeta = &proof.open_evals[0][0].into_plain_value().0;
    let s_zeta = &proof.open_evals[0][1].into_plain_value().0;
    let b_zeta = &proof.open_evals[0][2].into_plain_value().0;
    let q3_zeta = &proof.open_evals[0][7].into_plain_value().0;
    let b_zeta_omega = &proof.open_evals[2][0].into_plain_value().0;
    let last_root = domain.element(domain.size() - 1);
    // verify [B(zeta*w) * (A'(zeta) + beta) * (S'(zeta) + gamma) - B(zeta) * (A(zeta) + beta) * (S(zeta) + gamma)] * (zeta - w^{n-1}) = Z(zeta) * Q3(zeta)
    let lhs = (b_zeta_omega.mul(*a_prime_zeta + beta).mul(*s_prime_zeta + gamma) - b_zeta.mul(*a_zeta + beta).mul(*s_zeta + gamma)).mul(zeta - last_root);
    let rhs = z_zeta.mul(q3_zeta);
    assert_eq!(lhs, rhs);

    let q4_zeta = &proof.open_evals[0][8].into_plain_value().0;
    // verify (B(zeta) - 1) / [(zeta - w^0) * (zeta - w^{n-1})] = Q4(zeta)
    let lhs = *b_zeta - E::ScalarField::one();
    let rhs = q4_zeta.mul(zeta - E::ScalarField::one()).mul(zeta - last_root);
    assert_eq!(lhs, rhs);

    batch_check(vk, proof, rng);
}

fn prove_v2_permutation<E: Pairing>(
    a: &DensePolynomial<E::ScalarField>,
    s: &DensePolynomial<E::ScalarField>,
    a_prime: &DensePolynomial<E::ScalarField>,
    s_prime: &DensePolynomial<E::ScalarField>,
    cm_a: &Commitment<E>,
    cm_s: &Commitment<E>,
    cm_a_prime: &Commitment<E>,
    cm_s_prime: &Commitment<E>,
    domain: Radix2EvaluationDomain<E::ScalarField>,
) -> (DensePolynomial<E::ScalarField>, DensePolynomial<E::ScalarField>, DensePolynomial<E::ScalarField>) {
    let mut transcript = Transcript::new();
    transcript.append_affines::<E>(&vec![
        cm_a.0, cm_s.0, cm_a_prime.0, cm_s_prime.0,
    ]);
    let beta = transcript.append_and_digest::<E>("beta".to_string());
    let gamma = transcript.append_and_digest::<E>("gamma".to_string());

    let a_evals = a.clone().evaluate_over_domain(domain).evals;
    let s_evals = s.clone().evaluate_over_domain(domain).evals;
    let a_prime_evals = a_prime.clone().evaluate_over_domain(domain).evals;
    let s_prime_evals = s_prime.clone().evaluate_over_domain(domain).evals;

    // (A(X) + beta) * (S(X) + gamma)
    let a_s_beta_gamma: Vec<_> = a_evals.iter().zip(s_evals)
        .map(| (a, s) | {
            (*a + beta).mul(s + gamma)
        })
        .collect();

    // (A'(X) + beta) * (S'(X) + gamma)
    let a_s_prime_beta_gamma: Vec<_> = a_prime_evals.iter().zip(s_prime_evals)
        .map(| (a, s) | {
            (*a + beta).mul(s + gamma)
        })
        .collect();

    let b_evals = construct_accumulator_for_prod_check(&a_s_beta_gamma, &a_s_prime_beta_gamma);
    let mut b_shifted_evals = b_evals.clone();
    b_shifted_evals.rotate_left(1);
    // B(1) = B(X^{n-1}) = 1
    // B(Xw) = B(X) * (A(X) + beta) * (S(X) + gamma) / (A'(X) + beta) * (S'(X) + gamma)
    let b = Evaluations::from_vec_and_domain(b_evals, domain).interpolate();
    // B(Xw)
    let b_shifted = Evaluations::from_vec_and_domain(b_shifted_evals, domain).interpolate();
    // constant polynomials, beta and gamma
    let poly_beta = DensePolynomial::from_coefficients_vec(vec![beta]);
    let poly_gamma = DensePolynomial::from_coefficients_vec(vec![gamma]);
    // A'(X) + beta
    let a_prime_beta = a_prime + &poly_beta;
    // S'(X) + gamma
    let s_prime_gamma = s_prime + &poly_gamma;
    // A(X) + beta
    let a_beta = a + &poly_beta;
    // S(X) + gamma
    let s_gamma = s + &poly_gamma;
    // W3(X) = B(Xw) * [A'(X) + beta] * [S'(X) + gamma] - B(X) * [A(X) + beta] * [S(X) + gamma]
    let w3 = &(&b_shifted * &(&a_prime_beta * &s_prime_gamma)) - &(&b * &(&a_beta * &s_gamma));

    // w^{n-1}
    let last_root = domain.element(domain.size() - 1);
    // X - w^{n-1}
    let x_minus_last_root = DensePolynomial::from_coefficients_vec(vec![-last_root, E::ScalarField::one()]);
    // the vanishing polynomial Z(X)
    let z = DenseOrSparsePolynomial::from(domain.vanishing_polynomial());
    // Z(X) / (X - w^{n-1})
    let (q, r) = z.divide_with_q_and_r(&DenseOrSparsePolynomial::from(&x_minus_last_root)).unwrap();
    assert!(r.is_zero());
    // W3(X) * (X - w^{n-1}) / Z(X)
    let (q3, r) = DenseOrSparsePolynomial::from(w3).divide_with_q_and_r(&DenseOrSparsePolynomial::from(q)).unwrap();
    assert!(r.is_zero());

    // X - w^0
    let x_minus_one = DensePolynomial::from_coefficients_vec(vec![-E::ScalarField::one(), E::ScalarField::one()]);
    // W4(X) = B(X) - 1
    let w4 = &b - &DensePolynomial::from_coefficients_vec(vec![E::ScalarField::one()]);
    // Q4(X) = W4(X) / [(X - w^0) * (X - w^{n-1})]
    let (q4, r) = DenseOrSparsePolynomial::from(w4).divide_with_q_and_r(&DenseOrSparsePolynomial::from(&x_minus_last_root * &x_minus_one)).unwrap();
    assert!(r.is_zero());

    (b, q3, q4)
}

fn sort(
    a_evals: &Vec<u64>,
    s_evals: &Vec<u64>,
) -> (Vec<u64>, Vec<u64>) {
    // convert S from an array into a map
    let s_map: Vec<(u64, usize)> = s_evals.iter()
        .map(| val | {
            (*val, 1)
        })
        .collect();
    let mut s_map = BTreeMap::from_iter(s_map);

    // construct A' by copying A and sort A'
    let mut a_prime_evals = a_evals.clone();
    a_prime_evals.sort();

    // initialize S' by filling it with 0
    let mut s_prime_evals= Vec::<u64>::with_capacity(s_evals.len());
    for _ in 0..s_evals.len() { s_prime_evals.push(0); }

    let mut repeated_evals = vec![];

    // S'[0] = A'[0]
    s_prime_evals[0] = a_prime_evals[0];
    let x = s_map.get_mut(&a_prime_evals[0]).unwrap();
    *x -= 1;

    for i in 1..a_prime_evals.len() {
        let prev = a_prime_evals[i - 1];
        let cur = a_prime_evals[i];
        if prev == cur { 
            // when the current element is equal to the previous one, record the index and dont update S'
            repeated_evals.push(i);
        } else {
            // when the current element is different from the previous one, update S' and decrease the count
            s_prime_evals[i] = cur;
            let x = s_map.get_mut(&cur).unwrap();
            *x -= 1;
        }
    }

    for (val, count) in s_map {
        // fill S' with the elements not queried in the map
        if count == 1 {
            if let Some(idx) = repeated_evals.pop() {
                s_prime_evals[idx] = val;
            }
        }
    }

    (a_prime_evals, s_prime_evals)
}
