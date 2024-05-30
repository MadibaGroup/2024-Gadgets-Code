use std::ops::Mul;

use ark_ec::pairing::Pairing;
use ark_ff::{FftField, Zero};
use ark_poly::{univariate::{DenseOrSparsePolynomial, DensePolynomial}, DenseUVPolynomial, EvaluationDomain, Evaluations, Polynomial, Radix2EvaluationDomain};
use ark_poly_commit::kzg10::{Powers, VerifierKey, KZG10};
use ark_std::{rand::RngCore, One};

use crate::utils::{batch_check, batch_open, calculate_hash, BatchCheckProof, HashBox};

pub fn prove<E: Pairing, R: RngCore>(
    powers: &Powers<E>,
    values: &Vec<u64>,
    domain: Radix2EvaluationDomain<E:: ScalarField>,
    rng: &mut R,
) -> BatchCheckProof<E> {
    // compute polynomials, P_A(X), P_B(X) and Q(X), where Q(X) = [P_B(Xw) - P_A(X) * P_B(X)] * (X - w^{n-1}) / Z(X)
    let (pa, pb, q) = compute_polynomials::<E>(domain, values);

    // commit to P_A
    let (cm_pa, mask_pa) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &pa, 
            Some(pa.degree()), 
            Some(rng)
        ).unwrap();

    // commit to P_B
    let (cm_pb, mask_pb) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &pb,
            Some(pb.degree()), 
            Some(rng)
        ).unwrap();

    // commit to Q
    let (cm_q, mask_q) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &q, 
            Some(q.degree()), 
            Some(rng)
        ).unwrap();

    // calculate the challenge, tau
    let tau = calculate_hash(
        &vec![
                HashBox::<E>{ object: cm_pa.0 },
                HashBox::<E>{ object: cm_pb.0 },
                HashBox::<E>{ object: cm_q.0 },
            ]
        );

    // open the evaluations at tau for P_A, P_B and Q
    let (h1, open_evals1, gamma1) = batch_open(
        powers, 
        &vec![&pa, &pb, &q], 
        &vec![&mask_pa, &mask_pb, &mask_q], 
        tau, 
        false, 
        rng
    );

    let omega = domain.element(1);

    // open the evaluation at tau*omega for P_B
    let (h2, open_evals2, gamma2) = batch_open(
        powers, 
        &vec![&pb], 
        &vec![&mask_pb], 
        tau * omega, 
        false, 
        rng
    );

    // construct the proof
    BatchCheckProof {
        commitments: vec![
            vec![cm_pa, cm_pb, cm_q],
            vec![cm_pb],
        ],
        witnesses: vec![h1, h2],
        points: vec![tau, tau * omega],
        open_evals: vec![
            open_evals1,
            open_evals2,
        ],
        gammas: vec![gamma1, gamma2],
    }
}

pub fn verify<E: Pairing, R: RngCore>(
    vk: VerifierKey<E>,
    proof: BatchCheckProof<E>,
    domain: Radix2EvaluationDomain<E::ScalarField>,
    rng: &mut R,
) {
    let cm_pa = proof.commitments[0][0];
    let cm_pb = proof.commitments[0][1];
    let cm_q = proof.commitments[0][2];

    // verify tau is correct
    let tau = calculate_hash(
    &vec![
                HashBox::<E>{ object: cm_pa.0 },
                HashBox::<E>{ object: cm_pb.0 },
                HashBox::<E>{ object: cm_q.0 },
            ]
        );
    assert_eq!(tau, proof.points[0]);

    // verify tau*omega is correct
    let omega = domain.element(1);
    assert_eq!(tau * omega, proof.points[1]);

    // read the evaluations of P_A(tau), P_B(tau), Q(tau), P_B(tau*omega)
    let pa_tau = &proof.open_evals[0][0].into_plain_value().0;
    let pb_tau = &proof.open_evals[0][1].into_plain_value().0;
    let q_tau = &proof.open_evals[0][2].into_plain_value().0;
    let pb_tau_omega = &proof.open_evals[1][0].into_plain_value().0;

    // evaluate Z(X) at tau
    let z = domain.vanishing_polynomial();
    let z_tau = z.evaluate(&tau);

    // compute w^{n-1}
    let domain_size = domain.size as usize;
    let last_omega = domain.element(domain_size - 1);

    // verify [P_B(Xw) - P_A(X) * P_B(X)] * (X - w^{n-1}) = Z(X) * Q(X)
    let lhs = (*pb_tau - pb_tau_omega.mul(pa_tau)) * (tau - last_omega);
    let rhs = z_tau * q_tau;
    assert_eq!(lhs, rhs);

    batch_check(&vk, &proof, rng);
}

/// interpolate P_A(X), P_B(X) and compute Q(X) from the input values
fn compute_polynomials<E: Pairing>(
    domain: Radix2EvaluationDomain<E:: ScalarField>,
    values: &Vec<u64>,
) -> (DensePolynomial<E::ScalarField>, DensePolynomial<E::ScalarField>, DensePolynomial<E::ScalarField>) {
    let degree = values.len();
    let domain_size = domain.size as usize;
    
    // convert the values into field elements for P_A(X)
    let mut a_evals: Vec<E::ScalarField> = values.iter()
        .map(| val | {
            E::ScalarField::from(*val)
        })
        .collect();
    let ones = vec![E::ScalarField::one(); domain_size - degree];
    a_evals.extend(ones);

    // construct the accumulator for P_B(X)
    let b_evals = compute_accumulator(&a_evals);

    // rotate left the accumulator so that P_B(Xw) can be interpolated from the shifted evaluations
    let mut b_shifted_evals = b_evals.clone();
    b_shifted_evals.rotate_left(1);

    // interpolate polynomials P_A(X), P_B(X), P_B(Xw)
    let pa = Evaluations::from_vec_and_domain(a_evals, domain).interpolate();
    let pb = Evaluations::from_vec_and_domain(b_evals, domain).interpolate();
    let pb_shifted = Evaluations::from_vec_and_domain(b_shifted_evals, domain).interpolate();

    // construct the polynomial, X - w^{n-1}
    let last_omega = domain.element(domain_size - 1);
    let x_minus_last_omega = DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![-last_omega, E::ScalarField::one()]);

    // compute w = [P_B(Xw) - P_B(X)*P_A(X)] * (X - w^{degree-1})
    let mut w = &pb_shifted * &pa;
    w = &pb - &w;
    w = &w * &x_minus_last_omega;

    // the vanishing polynomial of this domain, X^n - 1
    let z = DenseOrSparsePolynomial::from(domain.vanishing_polynomial());

    // w / z, the remainder should be zero polynomial
    let (q, r) = DenseOrSparsePolynomial::from(w).divide_with_q_and_r(&z).unwrap();
    assert!(r.is_zero());

    (pa, pb, q)
}

fn compute_accumulator<F: FftField>(evals: &Vec<F>) -> Vec<F> {
    let len = evals.len();
    let mut acc = Vec::<F>::with_capacity(len);
    for _ in 0..len { acc.push(F::zero()); }
    acc[len - 1] = evals[len - 1];
    for i in (0..len - 1).rev() {
        acc[i] = acc[i + 1] * evals[i];
    }
    acc
}
