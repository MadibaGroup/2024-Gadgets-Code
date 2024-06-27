use std::ops::Mul;

use ark_ec::pairing::Pairing;
use ark_poly::{univariate::DensePolynomial, EvaluationDomain, Evaluations, Polynomial, Radix2EvaluationDomain};
use ark_poly_commit::kzg10::{Powers, VerifierKey, KZG10};
use ark_std::{rand::RngCore, One};

use crate::{prod_check, utils::{batch_open, calculate_hash, BatchCheckProof, HashBox}};

/// to prove F(X) = G(sigma(X)) on the domain
pub fn prove<E: Pairing, R: RngCore>(
    powers: &Powers<E>,
    f_evals: &Vec<E::ScalarField>,
    g_evals: &Vec<E::ScalarField>,
    s_evals: &Vec<E::ScalarField>,
    domain: Radix2EvaluationDomain<E:: ScalarField>,
    rng: &mut R,
) -> BatchCheckProof<E> {
    assert_eq!(f_evals.len(), g_evals.len());
    assert_eq!(f_evals.len(), s_evals.len());

    let degree = f_evals.len();
    let domain_size = domain.size as usize;

    let mut f_evals: Vec<E::ScalarField> = f_evals.clone();
    let mut g_evals: Vec<E::ScalarField> = g_evals.clone();
    let mut s_evals: Vec<E::ScalarField> = s_evals.clone();

    // in case that the number of input values is not the power of two, fill the left space with one, this doesn't break the completeness and soundness
    let ones = vec![E::ScalarField::one(); domain_size - degree];
    f_evals.extend(ones.clone());
    g_evals.extend(ones.clone());
    for i in 0..domain_size - degree {
        let omega = domain.element(i + degree);
        s_evals.push(omega);
    }

    // interpolate F(X), G(X), S(X)
    let f = Evaluations::from_vec_and_domain(f_evals.clone(), domain).interpolate();
    let g = Evaluations::from_vec_and_domain(g_evals.clone(), domain).interpolate();
    let s = Evaluations::from_vec_and_domain(s_evals.clone(), domain).interpolate();

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

    // commit to S(X)
    let (cm_s, mask_s) = 
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            &powers, 
            &s,
            Some(s.degree()), 
            Some(rng)
        ).unwrap();

    // calculate the challenges a and b
    let a = calculate_hash(
        &vec![
                HashBox::<E>{ object: cm_f.0 },
                HashBox::<E>{ object: cm_s.0 },
            ]
        );
    let b = calculate_hash(
        &vec![
                HashBox::<E>{ object: cm_g.0 },
                HashBox::<E>{ object: cm_s.0 },
            ]
        );

    // compute the evaluations such that the product of [a - b * S(X) - F(X)] and [a - b * X - G(X)]
    let numerator: Vec<_> = f_evals.iter().zip(s_evals)
        .map(| (f_eval, s_eval) | {
            a - b.mul(s_eval) - f_eval
        })
        .collect();
    let denominator: Vec<_> = g_evals.iter().enumerate()
        .map(| (i, g_eval) | {
            let omega = domain.element(i);
            a - b.mul(omega) - g_eval
        })
        .collect();

    // prove the product of r - F(X) is equal to r - G(X)
    let prod_check_proof = prod_check::prove(powers, &numerator, &denominator, domain, rng);

    let cm_numerator = prod_check_proof.commitments[0][0];
    let cm_denominator = prod_check_proof.commitments[0][1];
    let cm_t = prod_check_proof.commitments[0][2];
    let cm_q1 = prod_check_proof.commitments[0][3];
    let cm_q2 = prod_check_proof.commitments[0][4];

    // compute zeta
    let zeta = calculate_hash(
        &vec![
            HashBox::<E>{ object: cm_numerator.0 },
            HashBox::<E>{ object: cm_denominator.0 },
            HashBox::<E>{ object: cm_t.0 },
            HashBox::<E>{ object: cm_q1.0 },
            HashBox::<E>{ object: cm_q2.0 },
        ]
    );

    // open F(zeta) and G(zeta)
    let (h, open_evals, gamma) = batch_open(
        powers, 
        &vec![&f, &g, &s], 
        &vec![&mask_f, &mask_g, &mask_s], 
        zeta, 
        false, 
        rng
    );

    // append the proofs of F(zeta) and G(zeta)
    BatchCheckProof { 
        commitments: vec![
            prod_check_proof.commitments[0].clone(),
            prod_check_proof.commitments[1].clone(),
            prod_check_proof.commitments[2].clone(),
            vec![cm_f, cm_g, cm_s],
        ], 
        witnesses: prod_check_proof.witnesses.into_iter().chain(vec![h].into_iter()).collect(), 
        points: prod_check_proof.points.into_iter().chain(vec![zeta].into_iter()).collect(), 
        open_evals: prod_check_proof.open_evals.into_iter().chain(vec![open_evals].into_iter()).collect(), 
        gammas: prod_check_proof.gammas.into_iter().chain(vec![gamma].into_iter()).collect() 
    }
}

pub fn verify<E: Pairing, R: RngCore>(
    vk: VerifierKey<E>,
    proof: &BatchCheckProof<E>,
    domain: Radix2EvaluationDomain<E::ScalarField>,
    rng: &mut R,
) {
    let cm_f = proof.commitments[3][0];
    let cm_g = proof.commitments[3][1];
    let cm_s = proof.commitments[3][2];

    // calculate the challenges a and b
    let a = calculate_hash(
        &vec![
                HashBox::<E>{ object: cm_f.0 },
                HashBox::<E>{ object: cm_s.0 },
            ]
        );
    let b = calculate_hash(
        &vec![
                HashBox::<E>{ object: cm_g.0 },
                HashBox::<E>{ object: cm_s.0 },
            ]
        );

    let a_minus_bs_f_zeta = &proof.open_evals[0][0].into_plain_value().0;
    let a_minus_b_g_zeta = &proof.open_evals[0][1].into_plain_value().0;
    let f_zeta = &proof.open_evals[3][0].into_plain_value().0;
    let g_zeta = &proof.open_evals[3][1].into_plain_value().0;
    let s_zeta = &proof.open_evals[3][2].into_plain_value().0;

    let cm_numerator = proof.commitments[0][0];
    let cm_denominator = proof.commitments[0][1];
    let cm_t = proof.commitments[0][2];
    let cm_q1 = proof.commitments[0][3];
    let cm_q2 = proof.commitments[0][4];

    // compute zeta
    let zeta = calculate_hash(
        &vec![
            HashBox::<E>{ object: cm_numerator.0 },
            HashBox::<E>{ object: cm_denominator.0 },
            HashBox::<E>{ object: cm_t.0 },
            HashBox::<E>{ object: cm_q1.0 },
            HashBox::<E>{ object: cm_q2.0 },
        ]
    );

    // verify a - b * S(zeta) - F(zeta) and a - b * zeta - G(zeta) are correct
    assert_eq!(a - b.mul(s_zeta) - f_zeta, *a_minus_bs_f_zeta);
    assert_eq!(a - b.mul(zeta) - g_zeta, *a_minus_b_g_zeta);

    // perform the product check
    prod_check::verify(&vk, proof, domain, domain.size(), rng);
}
