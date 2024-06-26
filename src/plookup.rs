use std::ops::Mul;

use ark_ec::pairing::Pairing;
use ark_poly::{univariate::{DenseOrSparsePolynomial, DensePolynomial}, DenseUVPolynomial, EvaluationDomain, Evaluations, Polynomial, Radix2EvaluationDomain};
use ark_poly_commit::kzg10::{Commitment, Powers, VerifierKey, KZG10};
use ark_std::{rand::RngCore, One, Zero};

use crate::utils::{batch_check, batch_open, construct_accumulator_for_prod_check, shift_polynomial_left, BatchCheckProof, Transcript};

pub fn prove<E: Pairing, R: RngCore>(
    powers: &Powers<E>,
    a_evals: &Vec<u64>,
    t_evals: &Vec<u64>,
    domain: Radix2EvaluationDomain<E:: ScalarField>,
    rng: &mut R,
) -> BatchCheckProof<E> {
    let a_len = a_evals.len();
    let t_len = t_evals.len();
    assert_eq!(t_len, a_len + 1);
    let s_evals = merge(a_evals, t_evals);
    let s_l_evals = s_evals.as_slice()[0..a_len + 1].to_vec();
    let s_h_evals = s_evals.as_slice()[a_len..].to_vec();

    // convert the integer evaluations to group elements
    let a_evals: Vec<_> = a_evals.iter()
        .map(| eval| {
            E::ScalarField::from(*eval)
        })
        .collect();
    let t_evals: Vec<_> = t_evals.iter()
        .map(| eval| {
            E::ScalarField::from(*eval)
        })
        .collect();
    let s_l_evals: Vec<_> = s_l_evals.iter()
        .map(| eval| {
            E::ScalarField::from(*eval)
        })
        .collect();
    let s_h_evals: Vec<_> = s_h_evals.iter()
        .map(| eval| {
            E::ScalarField::from(*eval)
        })
        .collect();

    // A(X)
    let a = Evaluations::from_vec_and_domain(a_evals, domain).interpolate();
    // T(X)
    let t = Evaluations::from_vec_and_domain(t_evals, domain).interpolate();
    // S_l(X)
    let s_l = Evaluations::from_vec_and_domain(s_l_evals, domain).interpolate();
    // S_h(X)
    let s_h = Evaluations::from_vec_and_domain(s_h_evals, domain).interpolate();

    // commit to A(X)
    let (cm_a, mask_a) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &a, 
            Some(a.degree()), 
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

    // commit to S_l(X)
    let (cm_s_l, mask_s_l) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &s_l, 
            Some(s_l.degree()), 
            Some(rng)
        ).unwrap();

    // commit to S_h(X)
    let (cm_s_h, mask_s_h) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &s_h,
            Some(s_h.degree()), 
            Some(rng)
        ).unwrap();

    let (b, q2) = prove_permutation(&a, &t, &s_l, &s_h, &cm_a, &cm_t, &cm_s_l, &cm_s_h, domain);

    let one = E::ScalarField::one();
    let poly_one = DensePolynomial::from_coefficients_vec(vec![one]);
    // X - w^0
    let x_minus_one = DensePolynomial::from_coefficients_vec(vec![-one, one]);
    // X - w^{n-1]}
    let last_root = domain.element(domain.size() - 1);
    let x_minus_last_root = DensePolynomial::from_coefficients_vec(vec![-last_root, one]);
    // W1(X) = B(X) - 1
    let w1 = &b - &poly_one;
    // Q1(X) = W1(X) / [(X - w^0) * (X - w^{n-1})]
    let (q1, r) = DenseOrSparsePolynomial::from(w1).divide_with_q_and_r(&DenseOrSparsePolynomial::from(&x_minus_one * &x_minus_last_root)).unwrap();
    assert!(r.is_zero());

    let s_h_shifted = shift_polynomial_left(s_h.clone(), domain);
    // W3(X) = S_l(X) - S_h(Xw)
    let w3 = &s_l - &s_h_shifted;
    // Q3(X) = W3(X) / (X - w^{n-1})
    let (q3, r) = DenseOrSparsePolynomial::from(w3).divide_with_q_and_r(&DenseOrSparsePolynomial::from(x_minus_last_root)).unwrap();
    assert!(r.is_zero());

    // commit to B(X)
    let (cm_b, mask_b) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &b,
            Some(b.degree()), 
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

    // commit to Q3(X)
    let (cm_q3, mask_q3) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &q3,
            Some(q3.degree()), 
            Some(rng)
        ).unwrap();

    let mut transcript = Transcript::new();
    transcript.append_affines::<E>(&vec![
        cm_a.0, cm_t.0, cm_s_l.0, cm_s_h.0, cm_b.0, cm_q1.0, cm_q2.0, cm_q3.0,
    ]);
    let zeta = transcript.append_and_digest::<E>("zeta".to_string());

    // open the evaluations at Zeta for A, T, S_l, S_h, B, Q1, Q2, Q3
    let (h1, open_evals1, gamma1) = batch_open(
        powers, 
        &vec![&a, &t, &s_l, &s_h, &b, &q1, &q2, &q3], 
        &vec![&mask_a, &mask_t, &mask_s_l, &mask_s_h, &mask_b, &mask_q1, &mask_q2, &mask_q3], 
        zeta, 
        false, 
        rng
    );

    let omega = domain.element(1);

    // open the evaluation at zeta * omega for T, S_l, S_h, B
    let (h2, open_evals2, gamma2) = batch_open(
        powers, 
        &vec![&t, &s_l, &s_h, &b], 
        &vec![&mask_t, &mask_s_l, &mask_s_h, &mask_b], 
        zeta * omega, 
        false, 
        rng
    );

    BatchCheckProof {
        commitments: vec![
            vec![cm_a, cm_t, cm_s_l, cm_s_h, cm_b, cm_q1, cm_q2, cm_q3],
            vec![cm_t, cm_s_l, cm_s_h, cm_b],
        ],
        witnesses: vec![h1, h2],
        points: vec![zeta, zeta * omega],
        open_evals: vec![
            open_evals1,
            open_evals2,
        ],
        gammas: vec![gamma1, gamma2],
    }
}

pub fn verify<E: Pairing, R: RngCore>(
    vk: &VerifierKey<E>,
    proof: &BatchCheckProof<E>,
    domain: Radix2EvaluationDomain<E::ScalarField>,
    rng: &mut R,
) {
    let cm_a = proof.commitments[0][0];
    let cm_t = proof.commitments[0][1];
    let cm_s_l = proof.commitments[0][2];
    let cm_s_h = proof.commitments[0][3];
    let cm_b = proof.commitments[0][4];
    let cm_q1 = proof.commitments[0][5];
    let cm_q2 = proof.commitments[0][6];
    let cm_q3 = proof.commitments[0][7];

    // verify zeta is correct
    let mut transcript = Transcript::new();
    transcript.append_affines::<E>(&vec![
        cm_a.0, cm_t.0, cm_s_l.0, cm_s_h.0, cm_b.0, cm_q1.0, cm_q2.0, cm_q3.0,
    ]);
    let zeta = transcript.append_and_digest::<E>("zeta".to_string());
    assert_eq!(zeta, proof.points[0]);

    // verify zeta * omega is correct
    let omega = domain.element(1);
    assert_eq!(zeta * omega, proof.points[1]);

    let one = E::ScalarField::one();
    let last_root = domain.element(domain.size() - 1);

    let b_zeta = &proof.open_evals[0][4].into_plain_value().0;
    let q1_zeta = &proof.open_evals[0][5].into_plain_value().0;
    // verify [B(zeta) - 1] / [(zeta - w^0) * (zeta - w^{n-1})] = Q1(zeta)
    let lhs = *b_zeta - one;
    let rhs = (zeta - one).mul(zeta - last_root).mul(q1_zeta);
    assert_eq!(lhs, rhs);

    let b_zeta_omega = &proof.open_evals[1][3].into_plain_value().0;
    let s_l_zeta = &proof.open_evals[0][2].into_plain_value().0;
    let s_l_zeta_omega = &proof.open_evals[1][1].into_plain_value().0;
    let s_h_zeta = &proof.open_evals[0][3].into_plain_value().0;
    let s_h_zeta_omega = &proof.open_evals[1][2].into_plain_value().0;
    let a_zeta = &proof.open_evals[0][0].into_plain_value().0;
    let t_zeta = &proof.open_evals[0][1].into_plain_value().0;
    let t_zeta_omega = &proof.open_evals[1][0].into_plain_value().0;
    let q2_zeta = &proof.open_evals[0][6].into_plain_value().0;
    
    // compute alpha and beta by Fiat Shamir transformation
    let mut transcript = Transcript::new();
    transcript.append_affines::<E>(&vec![
        cm_a.0,
        cm_t.0,
        cm_s_l.0,
        cm_s_h.0,
    ]);
    
    let alpha = transcript.append_and_digest::<E>("alpha".to_string());
    let beta = transcript.append_and_digest::<E>("beta".to_string());
    // Z(zeta)
    let zed = domain.vanishing_polynomial();
    let z_zeta = zed.evaluate(&zeta);
    // verify {B(Xw) * [alpha * (1 + beta) + S_l(X) + beta * S_l(Xw)] * [alpha * (1 + beta) + S_h(X) + beta * S_h(Xw)] -
    //         B(X) * (1 + beta) * [alpha + A(X)] * [alpha * (1 + beta) + T(X) + beta * T(Xw)]} * (X - w^{n - 1})
    let lhs = b_zeta_omega.mul(alpha.mul(one + beta) + s_l_zeta + beta.mul(s_l_zeta_omega)).mul(alpha.mul(one + beta) + s_h_zeta + beta.mul(s_h_zeta_omega)) - b_zeta.mul(one + beta).mul(alpha + a_zeta).mul(alpha.mul(one + beta) + t_zeta + beta.mul(t_zeta_omega));
    let rhs = z_zeta.mul(q2_zeta);
    assert_eq!(lhs.mul(zeta - last_root), rhs);

    let q3_zeta = &proof.open_evals[0][7].into_plain_value().0;
    // verify [S_l(zeta) - S_h(zeta * omega)] / (zeta - w^{n-1}) = Q3(zeta)
    let lhs = *s_l_zeta - s_h_zeta_omega;
    let rhs = (zeta - last_root).mul(q3_zeta);
    assert_eq!(lhs, rhs);

    batch_check(vk, proof, rng);
}

fn prove_permutation<E: Pairing>(
    a: &DensePolynomial<E::ScalarField>,
    t: &DensePolynomial<E::ScalarField>,
    s_l: &DensePolynomial<E::ScalarField>,
    s_h: &DensePolynomial<E::ScalarField>,
    cm_a: &Commitment<E>,
    cm_t: &Commitment<E>,
    cm_s_l: &Commitment<E>,
    cm_s_h: &Commitment<E>,
    domain: Radix2EvaluationDomain<E::ScalarField>,
) -> (DensePolynomial<E::ScalarField>, DensePolynomial<E::ScalarField>) {
    let mut transcript = Transcript::new();
    transcript.append_affines::<E>(&vec![
        cm_a.0,
        cm_t.0,
        cm_s_l.0,
        cm_s_h.0,
    ]);
    // compute alpha and beta by Fiat Shamir transformation
    let alpha = transcript.append_and_digest::<E>("alpha".to_string());
    let beta = transcript.append_and_digest::<E>("beta".to_string());

    let a_evals = a.clone().evaluate_over_domain(domain).evals;
    let t_evals = t.clone().evaluate_over_domain(domain).evals;
    let s_l_evals = s_l.clone().evaluate_over_domain(domain).evals;
    let s_h_evals = s_h.clone().evaluate_over_domain(domain).evals;

    // compute the evaluations for the accumulator
    let one = E::ScalarField::one();
    let mut numerator = Vec::<E::ScalarField>::new();
    let mut denominator = Vec::<E::ScalarField>::new();
    for i in 0..a.len() - 1 {
        let a_eval = a_evals[i];
        let t_eval = t_evals[i];
        let t_next_eval = t_evals[i + 1];
        let s_l_eval = s_l_evals[i];
        let s_l_next_eval = s_l_evals[i + 1];
        let s_h_eval = s_h_evals[i];
        let s_h_next_eval = s_h_evals[i + 1];

        numerator.push((one + beta).mul(alpha + a_eval).mul(alpha.mul(one + beta) + t_eval + beta.mul(t_next_eval)));
        denominator.push((alpha.mul(one + beta) + s_l_eval + beta.mul(s_l_next_eval)).mul(alpha.mul(one + beta) + s_h_eval + beta.mul(s_h_next_eval)));
    }

    // interpolate the accumulator B(X)
    let b_evals = construct_accumulator_for_prod_check(&numerator, &denominator);
    let b = Evaluations::from_vec_and_domain(b_evals, domain).interpolate();
    // T(Xw)
    let t_shifted = shift_polynomial_left(t.clone(), domain);
    // S_l(Xw)
    let s_l_shifted = shift_polynomial_left(s_l.clone(), domain);
    // S_h(Xw)
    let s_h_shifted = shift_polynomial_left(s_h.clone(), domain);
    // B(Xw)
    let b_shifted = shift_polynomial_left(b.clone(), domain);
    // constant polynomial, alpha, beta, one
    let poly_alpha = DensePolynomial::from_coefficients_vec(vec![alpha]);
    let poly_beta = DensePolynomial::from_coefficients_vec(vec![beta]);
    let poly_one = DensePolynomial::from_coefficients_vec(vec![one]);
    // alpha * (1 + beta)
    let poly_alpha_times_one_beta = &poly_alpha * &(&poly_one + &poly_beta);
    // alpha * (1 + beta) + S_l(X) + beta * S_l(Xw)
    let s_l_term = &poly_alpha_times_one_beta + s_l + &poly_beta * &s_l_shifted;
    // alpha * (1 + beta) + S_h(X) + beta * S_h(Xw)
    let s_h_term = &poly_alpha_times_one_beta + s_h + &poly_beta * &s_h_shifted;
    // alpha * (1 + beta) + T(X) + beta * T(Xw)
    let t_term = &poly_alpha_times_one_beta + t + &poly_beta * &t_shifted;
    // B(Xw) * [alpha * (1 + beta) + S_l(X) + beta * S_l(Xw)] * [alpha * (1 + beta) + S_h(X) + beta * S_h(Xw)]
    let left =  &(&b_shifted * &s_l_term) * &s_h_term;
    // B(X) * (1 + beta) * [alpha + A(X)] * [alpha * (1 + beta) + T(X) + beta * T(Xw)]
    let right = &(&(&b * &(&poly_one + &poly_beta)) * &(&poly_alpha + a)) * &t_term;
    // last root of unity
    let last_root = domain.element(domain.size() - 1);
    // X - w^{n-1}
    let x_minus_last_root = DensePolynomial::from_coefficients_vec(vec![-last_root, one]);
    // W2(X) = {B(Xw) * [alpha * (1 + beta) + S_l(X) + beta * S_l(Xw)] * [alpha * (1 + beta) + S_h(X) + beta * S_h(Xw)] -
    //         B(X) * (1 + beta) * [alpha + A(X)] * [alpha * (1 + beta) + T(X) + beta * T(Xw)]} * (X - w^{n - 1})
    let w2 = &(&left - &right) * &x_minus_last_root;
    // Z(X)
    let zed = DenseOrSparsePolynomial::from(domain.vanishing_polynomial());
    let (q2, r) = DenseOrSparsePolynomial::from(w2).divide_with_q_and_r(&zed).unwrap();
    assert!(r.is_zero());
    (b, q2)
}

fn merge(a_evals: &Vec<u64>, t_evals: &Vec<u64>) -> Vec<u64> {
    let mut a_evals = a_evals.clone();
    a_evals.sort();
    let mut t_evals = t_evals.clone();
    t_evals.sort();
    let mut i = 0;
    let mut j = 0;
    let mut s = Vec::<u64>::new();
    while i < a_evals.len() && j < t_evals.len() {
        let a = a_evals[i];
        let t = t_evals[j];
        if a <= t {
            s.push(a);
            i += 1;
        } else {
            s.push(t);
            j += 1;
        }
    }
    while i < a_evals.len() {
        let a = a_evals[i];
        s.push(a);
        i += 1;
    }
    while j < t_evals.len() {
        let t = t_evals[j];
        s.push(t);
        j += 1;
    }
    s
}
