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
    // compute polynomials, P_A(X), P_B(X), Q1(X) and Q2(X)
    // where Q1(X) = [P_B(Xw) - P_A(X) * P_B(X)] * (X - w^{n-1}) / Z(X)
    // Q2(X) = [P_A(X) - P_B(X)] * Z(X) / (X - w^{degree-1})
    let (pa, pb, q1, q2) = compute_polynomials::<E>(domain, values);

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

    // calculate the challenge, tau
    let tau = calculate_hash(
        &vec![
                HashBox::<E>{ object: cm_pa.0 },
                HashBox::<E>{ object: cm_pb.0 },
                HashBox::<E>{ object: cm_q1.0 },
                HashBox::<E>{ object: cm_q2.0 },
            ]
        );

    // open the evaluations at tau for P_A, P_B, Q1 and Q2
    let (h1, open_evals1, gamma1) = batch_open(
        powers, 
        &vec![&pa, &pb, &q1, &q2], 
        &vec![&mask_pa, &mask_pb, &mask_q1, &mask_q2], 
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

    // open the evaluation at 1 for P_B, i.e., the product
    let (h3, open_evals3, gamma3) = batch_open(
        powers, 
        &vec![&pb], 
        &vec![&mask_pb], 
        E::ScalarField::one(), 
        false, 
        rng
    );

    // construct the proof
    BatchCheckProof {
        commitments: vec![
            vec![cm_pa, cm_pb, cm_q1, cm_q2],
            vec![cm_pb],
            vec![cm_pb],
        ],
        witnesses: vec![h1, h2, h3],
        points: vec![tau, tau * omega, E::ScalarField::one()],
        open_evals: vec![
            open_evals1,
            open_evals2,
            open_evals3,
        ],
        gammas: vec![gamma1, gamma2, gamma3],
    }
}

/// verify the product is correct
pub fn verify_product<E: Pairing>(
    values: &Vec<u64>,
    proof: &BatchCheckProof<E>,
) {
    let prod: E::ScalarField = values.iter()
        .map(| val | E::ScalarField::from(*val))
        .product();
    assert_eq!(prod, proof.open_evals[2][0].into_plain_value().0);
}

/// verify the evaluations are correct and polynomials are vanishing
pub fn verify_evaluations<E: Pairing, R: RngCore>(
    vk: VerifierKey<E>,
    proof: &BatchCheckProof<E>,
    domain: Radix2EvaluationDomain<E::ScalarField>,
    degree: usize,
    rng: &mut R,
) {
    let cm_pa = proof.commitments[0][0];
    let cm_pb = proof.commitments[0][1];
    let cm_q1 = proof.commitments[0][2];
    let cm_q2 = proof.commitments[0][3];

    // verify tau is correct
    let tau = calculate_hash(
            &vec![
                HashBox::<E>{ object: cm_pa.0 },
                HashBox::<E>{ object: cm_pb.0 },
                HashBox::<E>{ object: cm_q1.0 },
                HashBox::<E>{ object: cm_q2.0 },
            ]
        );
    assert_eq!(tau, proof.points[0]);

    // verify tau*omega is correct
    let omega = domain.element(1);
    assert_eq!(tau * omega, proof.points[1]);

    // read the evaluations of P_A(tau), P_B(tau), Q1(tau), P_B(tau*omega)
    let pa_tau = &proof.open_evals[0][0].into_plain_value().0;
    let pb_tau = &proof.open_evals[0][1].into_plain_value().0;
    let q1_tau = &proof.open_evals[0][2].into_plain_value().0;
    let pb_tau_omega = &proof.open_evals[1][0].into_plain_value().0;

    // evaluate Z(X) at tau
    let z = domain.vanishing_polynomial();
    let z_tau = z.evaluate(&tau);

    // compute w^{n-1}
    let domain_size = domain.size as usize;
    let last_omega = domain.element(domain_size - 1);

    // verify [P_B(X) - P_B(Xw) * P_A(X)] * (X - w^{n-1}) = Z(X) * Q1(X)
    let lhs = (*pb_tau - pb_tau_omega.mul(pa_tau)) * (tau - last_omega);
    let rhs = z_tau * q1_tau;
    assert_eq!(lhs, rhs);

    // compute w^{degree-1}
    let omega_degree = domain.element(degree - 1);

    // read the evaluation of Q2(tau)
    let q2_tau = &proof.open_evals[0][3].into_plain_value().0;

    // verify [P_A(X) - P_B(X)] / (X - w^{degree-1}) = Q2(X)
    let lhs = (*pa_tau - pb_tau) / (tau - omega_degree);
    let rhs = *q2_tau;
    assert_eq!(lhs, rhs);

    batch_check(&vk, &proof, rng);
}

/// interpolate P_A(X), P_B(X) and compute Q(X) from the input values
fn compute_polynomials<E: Pairing>(
    domain: Radix2EvaluationDomain<E:: ScalarField>,
    values: &Vec<u64>,
) -> (DensePolynomial<E::ScalarField>, DensePolynomial<E::ScalarField>, DensePolynomial<E::ScalarField>, DensePolynomial<E::ScalarField>) {
    let degree = values.len();
    let domain_size = domain.size as usize;
    
    // convert the values into field elements for P_A(X)
    let mut a_evals: Vec<E::ScalarField> = values.iter()
        .map(| val | {
            E::ScalarField::from(*val)
        })
        .collect();
    // in case that the number of input values is not the power of two, fill the left space with one, this doesn't break the completeness/soundness
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

    // compute W_1(X) = [P_B(X) - P_B(Xw) * P_A(X)] * (X - w^{n-1})
    let mut w1 = &pb_shifted * &pa;
    w1 = &pb - &w1;
    w1 = &w1 * &x_minus_last_omega;

    // the vanishing polynomial of this domain, X^n - 1
    let z = DenseOrSparsePolynomial::from(domain.vanishing_polynomial());

    // W_1(X) / Z(X), the remainder should be zero polynomial
    let (q1, r) = DenseOrSparsePolynomial::from(w1).divide_with_q_and_r(&z).unwrap();
    assert!(r.is_zero());

    // construct the polynomial, X - w^{degree-1}
    let omega_degree = domain.element(degree - 1);
    let x_minus_omega_degree = DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![-omega_degree, E::ScalarField::one()]);

    // compute Z(X) / (X - w^{degree-1})
    let (zed, r) = z.divide_with_q_and_r(&DenseOrSparsePolynomial::from(x_minus_omega_degree)).unwrap();
    assert!(r.is_zero());

    // compute W_2(X) = [P_A(X) - P_B(X)] * Z(X) / (X - w^{degree-1})
    let mut w2 = &pa - &pb;
    w2 = &w2 * &zed;

    // W_2(X) / Z(X), the remainder should be zero polynomial
    let (q2, r) = DenseOrSparsePolynomial::from(w2).divide_with_q_and_r(&z).unwrap();
    assert!(r.is_zero());

    (pa, pb, q1, q2)
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
