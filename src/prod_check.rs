use std::ops::Mul;

use ark_ec::pairing::Pairing;
use ark_ff::FftField;
use ark_poly::{univariate::{DenseOrSparsePolynomial, DensePolynomial}, DenseUVPolynomial, EvaluationDomain, Evaluations, Polynomial, Radix2EvaluationDomain};
use ark_poly_commit::kzg10::{Powers, VerifierKey, KZG10};
use ark_std::{rand::RngCore, One, Zero};

use crate::utils::{batch_check, batch_open, calculate_hash, BatchCheckProof, HashBox};

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

    // calculate the challenge, xi
    let xi = calculate_hash(
        &vec![
                HashBox::<E>{ object: cm_f.0 },
                HashBox::<E>{ object: cm_g.0 },
                HashBox::<E>{ object: cm_t.0 },
                HashBox::<E>{ object: cm_q1.0 },
                HashBox::<E>{ object: cm_q2.0 },
            ]
        );

    // open the evaluations at xi for F, G, T, Q1 and Q2
    let (h1, open_evals1, gamma1) = batch_open(
        powers, 
        &vec![&f, &g, &t, &q1, &q2], 
        &vec![&mask_f, &mask_g, &mask_t, &mask_q1, &mask_q2], 
        xi, 
        false, 
        rng
    );

    let omega = domain.element(1);

    // open the evaluation at xi*omega for T
    let (h2, open_evals2, gamma2) = batch_open(
        powers, 
        &vec![&t], 
        &vec![&mask_t], 
        xi * omega, 
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
        points: vec![xi, xi * omega, E::ScalarField::one()],
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
    vk: VerifierKey<E>,
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

    // verify xi is correct
    let xi = calculate_hash(
            &vec![
                HashBox::<E>{ object: cm_f.0 },
                HashBox::<E>{ object: cm_g.0 },
                HashBox::<E>{ object: cm_t.0 },
                HashBox::<E>{ object: cm_q1.0 },
                HashBox::<E>{ object: cm_q2.0 },
            ]
        );
    assert_eq!(xi, proof.points[0]);

    // verify xi*omega is correct
    let omega = domain.element(1);
    assert_eq!(xi * omega, proof.points[1]);

    // read the evaluations of F(xi), G(xi), T(xi), Q1(xi), T(xi*omega)
    let f_xi = &proof.open_evals[0][0].into_plain_value().0;
    let g_xi = &proof.open_evals[0][1].into_plain_value().0;
    let t_xi = &proof.open_evals[0][2].into_plain_value().0;
    let q1_xi = &proof.open_evals[0][3].into_plain_value().0;
    let t_xi_omega = &proof.open_evals[1][0].into_plain_value().0;

    // evaluate Z(X) at xi
    let z = domain.vanishing_polynomial();
    let z_xi = z.evaluate(&xi);

    // compute w^{n-1}
    let domain_size = domain.size as usize;
    let last_omega = domain.element(domain_size - 1);

    // verify [T(X) * G(X) - T(Xw) * F(X)] * (X - w^{n-1}) = Z(X) * Q1(X)
    let lhs = (t_xi.mul(g_xi) - t_xi_omega.mul(f_xi)) * (xi - last_omega);
    let rhs = z_xi * q1_xi;
    assert_eq!(lhs, rhs);

    // compute w^{degree-1}
    let omega_degree = domain.element(degree - 1);

    // read the evaluation of Q2(xi)
    let q2_xi = &proof.open_evals[0][4].into_plain_value().0;

    // verify T(X) * G(X) - F(X) = Q2(X) * (X - w^{degree-1})
    let lhs = t_xi.mul(g_xi) - f_xi;
    let rhs = q2_xi.mul(xi - omega_degree);
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

    // compute the auxiliary polynomial such that T(X) = \prod{F(X)/G(X)}
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
