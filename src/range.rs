use std::ops::Mul;

use ark_ec::pairing::Pairing;
use ark_poly::{univariate::{DenseOrSparsePolynomial, DensePolynomial}, DenseUVPolynomial, EvaluationDomain, Evaluations, Polynomial, Radix2EvaluationDomain};
use ark_poly_commit::kzg10::{Powers, VerifierKey, KZG10};
use ark_std::{rand::RngCore, One, Zero};

use crate::utils::{batch_check, batch_open, BatchCheckProof, Transcript};

pub fn prove<E: Pairing, R: RngCore>(
    powers: &Powers<E>,
    n: u32,
    domain: Radix2EvaluationDomain<E:: ScalarField>,
    rng: &mut R,
) -> BatchCheckProof<E> {
    // decompose n into digits
    let digits = decompose_to_digits(n);
    let digits: Vec<_> = digits.iter()
        .map(| val | {
            E::ScalarField::from(*val)
        })
        .collect();

    let t = Evaluations::from_vec_and_domain(digits, domain).interpolate();
    let (q1, q2) = compute_polynomials::<E>(&t, domain);

    // commit to T(X)
    let (cm_t, mask_t) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &t, 
            Some(t.degree()), 
            Some(rng)
        ).unwrap();
    
    // commit to Q1(X)
    let (cm_q1, mask_q1) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &q1, 
            Some(q1.degree()), 
            Some(rng)
        ).unwrap();
    
    // commit to Q2(X)
    let (cm_q2, mask_q2) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &q2, 
            Some(q2.degree()), 
            Some(rng)
        ).unwrap();

    let mut transcript = Transcript::new();
    transcript.append_affines::<E>(&vec![
        cm_t.0, cm_q1.0, cm_q2.0,
    ]);
    let zeta = transcript.append_and_digest::<E>("zeta".to_string());

    let (h1, open_evals1, gamma1) = batch_open(
        powers, 
        &vec![&t, &q1, &q2], 
        &vec![&mask_t, &mask_q1, &mask_q2], 
        zeta, 
        false,
        rng
    );

    let omega = domain.element(1);
    let (h2, open_evals2, gamma2) = batch_open(
        powers, 
        &vec![&t], 
        &vec![&mask_t],
        zeta * omega, 
        false,
        rng
    );

    let (h3, open_evals3, gamma3) = batch_open(
        powers, 
        &vec![&t], 
        &vec![&mask_t], 
        E::ScalarField::one(), 
        false,
        rng
    );

    BatchCheckProof {
        commitments: vec![
            vec![cm_t, cm_q1, cm_q2],
            vec![cm_t],
            vec![cm_t],
        ],
        witnesses: vec![h1, h2, h3],
        points: vec![zeta, zeta * omega, E::ScalarField::one()],
        open_evals: vec![
            open_evals1,
            open_evals2,
            open_evals3,
        ],
        gammas: vec![gamma1, gamma2, gamma3],
    }
}

pub fn verify<E: Pairing, R: RngCore>(
    vk: VerifierKey<E>,
    proof: &BatchCheckProof<E>,
    domain: Radix2EvaluationDomain<E::ScalarField>,
    rng: &mut R,
) {
    let cm_t = proof.commitments[0][0];
    let cm_q1 = proof.commitments[0][1];
    let cm_q2 = proof.commitments[0][2];

    // verify zeta is correct
    let mut transcript = Transcript::new();
    transcript.append_affines::<E>(&vec![
        cm_t.0, cm_q1.0, cm_q2.0,
    ]);
    let zeta = transcript.append_and_digest::<E>("zeta".to_string());
    assert_eq!(zeta, proof.points[0]);

    // verify zeta * omega is correct
    let omega = domain.element(1);
    assert_eq!(zeta * omega, proof.points[1]);

    // read the evaluations of T(zeta), T(zeta * omega), Q1(zeta), Q2(zeta)
    let t_zeta = proof.open_evals[0][0].into_plain_value().0;
    let q1_zeta = proof.open_evals[0][1].into_plain_value().0;
    let q2_zeta = proof.open_evals[0][2].into_plain_value().0;
    let t_zeta_omega = proof.open_evals[1][0].into_plain_value().0;

    // evaluate Z(X) at zeta
    let z = domain.vanishing_polynomial();
    let z_zeta = z.evaluate(&zeta);

    // compute w^{n-1}
    let domain_size = domain.size as usize;
    let last_root = domain.element(domain_size - 1);
    
    let one = E::ScalarField::one();
    // verify T(zeta) * [T(zeta) - 1] * Z(zeta) / (zeta - w^{k-1}) = Q1(zeta) * Z(zeta)
    let lhs = t_zeta.mul(t_zeta - one).mul(z_zeta) / (zeta - last_root);
    let rhs = q1_zeta.mul(z_zeta);
    assert_eq!(lhs, rhs);

    let two = E::ScalarField::from(2u32);
    // verify [T(zeta) - 2 * T(zeta * omega)] * [T(zeta) - 2 * T(zeta * omega) - 1] * (zeta - w^{k-1}) = Q2(zeta) * Z(zeta)
    let lhs = (t_zeta - two * t_zeta_omega).mul(t_zeta - two * t_zeta_omega - one).mul(zeta - last_root);
    let rhs = q2_zeta.mul(z_zeta);
    assert_eq!(lhs, rhs);

    batch_check(&vk, proof, rng);
}

fn decompose_to_digits(n: u32) -> Vec<u32> {
    let mut digits = Vec::<u32>::new();
    let mut n = n;
    while n > 0 {
        digits.push(n);
        n = n >> 1;
    }
    digits
}

fn compute_polynomials<E: Pairing>(
    t: &DensePolynomial<E::ScalarField>,
    domain: Radix2EvaluationDomain<E:: ScalarField>
) -> (DensePolynomial<E::ScalarField>, DensePolynomial<E::ScalarField>) {
    // get the evaluations of T(X) over domain
    let t_evals = t.clone().evaluate_over_domain(domain);

    // compute the evaluations of T(Xw) over domain
    let mut t_shifted_evals = t_evals.evals.clone();
    t_shifted_evals.rotate_left(1);
    // interpolate T(Xw) from the evaluations
    let t_shifted = Evaluations::from_vec_and_domain(t_shifted_evals, domain).interpolate();

    // w^{k-1}
    let last_root = domain.element(domain.size() - 1);
    // construct X - w^{k-1}
    let x_minus_last_root = DenseOrSparsePolynomial::from(DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![-last_root, E::ScalarField::one()]));
    // constant polynomial, 1
    let one = DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![E::ScalarField::one()]);

    let zed = DenseOrSparsePolynomial::from(domain.vanishing_polynomial());

    // T(X) - 1
    let t_minus_1 = t - &one;
    // W1(X) = T(X) * [T(X) - 1]
    let w1 = &t_minus_1 * t;
    // Q1(X) = W1(X) / (X - w^{k-1})
    let (q1, r) = DenseOrSparsePolynomial::from(w1).divide_with_q_and_r(&x_minus_last_root).unwrap();
    assert!(r.is_zero());

    // constant polynomial, 2
    let two = DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![E::ScalarField::from(2u32)]);
    // T(X) - 2 * T(Xw)
    let t_minus_2_t_shifted = t - &(&two * &t_shifted);
    // W2(X) = [T(X) - 2 * T(Xw)] * [T(X) - 2 * T(Xw) - 1]
    let w2 = &t_minus_2_t_shifted * &(&t_minus_2_t_shifted - &one);
    // Z(X) / (X - w^{k-1})
    let (numerator, r) = zed.divide_with_q_and_r(&x_minus_last_root).unwrap();
    assert!(r.is_zero());
    // Q2(X) = W2(X) / [Z(X) / (X - w^{k-1})]
    let (q2, r) = DenseOrSparsePolynomial::from(w2).divide_with_q_and_r(&DenseOrSparsePolynomial::from(numerator)).unwrap();
    assert!(r.is_zero());

    (q1, q2)
}
