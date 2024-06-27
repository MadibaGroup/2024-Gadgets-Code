use std::ops::Mul;

use ark_ec::pairing::Pairing;
use ark_ff::FftField;
use ark_poly::{univariate::{DenseOrSparsePolynomial, DensePolynomial}, DenseUVPolynomial, EvaluationDomain, Evaluations, Polynomial, Radix2EvaluationDomain};
use ark_poly_commit::kzg10::{Powers, VerifierKey, KZG10};
use ark_std::{rand::RngCore, One, Zero};

use crate::utils::{batch_check, batch_open, BatchCheckProof, Transcript};

/// to prove the product of F(X) is equal to the product of g(X)
/// normally used for permutation check
pub fn prove<E: Pairing, R: RngCore>(
    powers: &Powers<E>,
    f_evals: &Vec<E::ScalarField>,
    g_evals: &Vec<E::ScalarField>,
    domain: Radix2EvaluationDomain<E:: ScalarField>,
    rng: &mut R,
) -> BatchCheckProof<E> {
    // compute polynomials, F(X), G(X), T(X), Q1(X) and Q2(X)
    // where Q1(X) = [T(X) * G(X) - T(Xw) * F(X)] * (X - w^{n-1}) / Z(X)
    // Q2(X) = [T(X) * G(X) - F(X)] / (X - w^{degree-1})
    let (f, g, t, q1, q2) = compute_polynomials::<E>(domain, f_evals, g_evals);

    // commit to F(X)
    let (cm_f, mask_f) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &f, 
            Some(f.degree()), 
            Some(rng)
        ).unwrap();

    // commit to G(X)
    let (cm_g, mask_g) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &g,
            Some(g.degree()), 
            Some(rng)
        ).unwrap();

    // commit to T(X)
    let (cm_t, mask_t) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &t,
            Some(t.degree()), 
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
        cm_f.0, cm_g.0, cm_t.0, cm_q1.0, cm_q2.0,
    ]);
    let zeta = transcript.append_and_digest::<E>("zeta".to_string());

    // open the evaluations at zeta for F, G, T, Q1 and Q2
    let (h1, open_evals1, gamma1) = batch_open(
        powers, 
        &vec![&f, &g, &t, &q1, &q2], 
        &vec![&mask_f, &mask_g, &mask_t, &mask_q1, &mask_q2], 
        zeta, 
        false, 
        rng
    );

    let omega = domain.element(1);

    // open the evaluation at zeta*omega for T
    let (h2, open_evals2, gamma2) = batch_open(
        powers, 
        &vec![&t], 
        &vec![&mask_t], 
        zeta * omega, 
        false, 
        rng
    );

    // open the evaluation at 1 for T
    let (h3, open_evals3, gamma3) = batch_open(
        powers, 
        &vec![&t], 
        &vec![&mask_t], 
        E::ScalarField::one(), 
        false, 
        rng
    );

    // construct the proof
    BatchCheckProof {
        commitments: vec![
            vec![cm_f, cm_g, cm_t, cm_q1, cm_q2],
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

/// verify the evaluations are correct and polynomials are vanishing
pub fn verify<E: Pairing, R: RngCore>(
    vk: &VerifierKey<E>,
    proof: &BatchCheckProof<E>,
    domain: Radix2EvaluationDomain<E::ScalarField>,
    degree: usize,
    rng: &mut R,
) {
    assert_eq!(E::ScalarField::one(), proof.open_evals[2][0].into_plain_value().0);

    let cm_f = proof.commitments[0][0];
    let cm_g = proof.commitments[0][1];
    let cm_t = proof.commitments[0][2];
    let cm_q1 = proof.commitments[0][3];
    let cm_q2 = proof.commitments[0][4];

    // verify zeta is correct
    let mut transcript = Transcript::new();
    transcript.append_affines::<E>(&vec![
        cm_f.0, cm_g.0, cm_t.0, cm_q1.0, cm_q2.0,
    ]);
    let zeta = transcript.append_and_digest::<E>("zeta".to_string());
    assert_eq!(zeta, proof.points[0]);

    // verify zeta*omega is correct
    let omega = domain.element(1);
    assert_eq!(zeta * omega, proof.points[1]);

    // read the evaluations of F(zeta), G(zeta), T(zeta), Q1(zeta), T(zeta*omega)
    let f_zeta = &proof.open_evals[0][0].into_plain_value().0;
    let g_zeta = &proof.open_evals[0][1].into_plain_value().0;
    let t_zeta = &proof.open_evals[0][2].into_plain_value().0;
    let q1_zeta = &proof.open_evals[0][3].into_plain_value().0;
    let t_zeta_omega = &proof.open_evals[1][0].into_plain_value().0;

    // evaluate Z(X) at zeta
    let z = domain.vanishing_polynomial();
    let z_zeta = z.evaluate(&zeta);

    // compute w^{n-1}
    let domain_size = domain.size as usize;
    let last_omega = domain.element(domain_size - 1);

    // verify [T(X) * G(X) - T(Xw) * F(X)] * (X - w^{n-1}) = Z(X) * Q1(X)
    let lhs = (t_zeta.mul(g_zeta) - t_zeta_omega.mul(f_zeta)) * (zeta - last_omega);
    let rhs = z_zeta * q1_zeta;
    assert_eq!(lhs, rhs);

    // compute w^{degree-1}
    let omega_degree = domain.element(degree - 1);

    // read the evaluation of Q2(zeta)
    let q2_zeta = &proof.open_evals[0][4].into_plain_value().0;

    // verify T(X) * G(X) - F(X) = Q2(X) * (X - w^{degree-1})
    let lhs = t_zeta.mul(g_zeta) - f_zeta;
    let rhs = q2_zeta.mul(zeta - omega_degree);
    assert_eq!(lhs, rhs);

    batch_check(&vk, &proof, rng);
}

fn compute_polynomials<E: Pairing>(
    domain: Radix2EvaluationDomain<E:: ScalarField>,
    f_evals: &Vec<E::ScalarField>,
    g_evals: &Vec<E::ScalarField>,
) -> (DensePolynomial<E::ScalarField>, DensePolynomial<E::ScalarField>, DensePolynomial<E::ScalarField>, DensePolynomial<E::ScalarField>, DensePolynomial<E::ScalarField>) {
    // the degrees of the two polynomials should be equal
    assert_eq!(f_evals.len(), g_evals.len());

    let degree = f_evals.len();
    let domain_size = domain.size as usize;

    let mut f_evals: Vec<E::ScalarField> = f_evals.clone();
    let mut g_evals: Vec<E::ScalarField> = g_evals.clone();

    // in case that the number of input values is not the power of two, fill the left space with one, this doesn't break the completeness and soundness
    let ones = vec![E::ScalarField::one(); domain_size - degree];
    f_evals.extend(ones.clone());
    g_evals.extend(ones.clone());

    // compute the auzetaliary polynomial such that T(X) = \prod{F(X)/G(X)}
    let t_evals = compute_aux_poly(&f_evals, &g_evals);

    // rotate left the accumulator so that T(Xw) can be interpolated from the shifted evaluations
    let mut t_shifted_evals = t_evals.clone();
    t_shifted_evals.rotate_left(1);

    // interpolate polynomials F(X), G(X), T(X), T(Xw)
    let f = Evaluations::from_vec_and_domain(f_evals, domain).interpolate();
    let g = Evaluations::from_vec_and_domain(g_evals, domain).interpolate();
    let t = Evaluations::from_vec_and_domain(t_evals, domain).interpolate();
    let t_shifted = Evaluations::from_vec_and_domain(t_shifted_evals, domain).interpolate();

    // construct the polynomial, X - w^{n-1}
    let last_omega = domain.element(domain_size - 1);
    let x_minus_last_omega = DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![-last_omega, E::ScalarField::one()]);

    // compute W_1(X) = [T(X) * G(X) - T(Xw) * F(X)] * (X - w^{n-1})
    let mut w1 = &t * &g;
    w1 = &w1 - &(&t_shifted * &f);
    w1 = &w1 * &x_minus_last_omega;

    // the vanishing polynomial of this domain, X^n - 1
    let z = DenseOrSparsePolynomial::from(domain.vanishing_polynomial());

    // W_1(X) / Z(X), the remainder should be zero polynomial
    let (q1, r) = DenseOrSparsePolynomial::from(w1).divide_with_q_and_r(&z).unwrap();
    assert!(r.is_zero());

    // construct the polynomial, X - w^{degree-1}
    let omega_degree = domain.element(degree - 1);
    let x_minus_omega_degree = DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![-omega_degree, E::ScalarField::one()]);

    // compute W_2(X) = T(X) * G(X) - F(X)
    let mut w2 = &t * &g;
    w2 = &w2 - &f;

    // W_2(X) / (X - w^{degree-1}), the remainder should be zero polynomial
    let (q2, r) = DenseOrSparsePolynomial::from(w2).divide_with_q_and_r(&DenseOrSparsePolynomial::from(x_minus_omega_degree)).unwrap();
    assert!(r.is_zero());

    (f, g, t, q1, q2)
}

fn compute_aux_poly<F: FftField>(
    f_evals: &Vec<F>,
    g_evals: &Vec<F>,
) -> Vec<F> {
    // the degrees of f and g should be equal
    assert_eq!(f_evals.len(), g_evals.len());

    let len = f_evals.len();
    let mut aux = Vec::<F>::with_capacity(len);
    for _ in 0..len { aux.push(F::zero()); }
    aux[len - 1] = f_evals[len - 1] / g_evals[len - 1];
    for i in (0..len - 1).rev() {
        aux[i] = aux[i + 1] * f_evals[i] / g_evals[i];
    }
    aux
}
