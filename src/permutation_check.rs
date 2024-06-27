use ark_ec::pairing::Pairing;
use ark_poly::{univariate::DensePolynomial, EvaluationDomain, Evaluations, Polynomial, Radix2EvaluationDomain};
use ark_poly_commit::kzg10::{Powers, VerifierKey, KZG10};
use ark_std::{rand::RngCore, One};

use crate::{prod_check, utils::{batch_open, BatchCheckProof, Transcript}};

/// to prove the evaluations of F(X) are the permutation of the evaluations of G(X)
pub fn prove<E: Pairing, R: RngCore>(
    powers: &Powers<E>,
    f_evals: &Vec<E::ScalarField>,
    g_evals: &Vec<E::ScalarField>,
    domain: Radix2EvaluationDomain<E:: ScalarField>,
    rng: &mut R,
) -> BatchCheckProof<E> {
    assert_eq!(f_evals.len(), g_evals.len());

    let degree = f_evals.len();
    let domain_size = domain.size as usize;

    let mut f_evals: Vec<E::ScalarField> = f_evals.clone();
    let mut g_evals: Vec<E::ScalarField> = g_evals.clone();

    // in case that the number of input values is not the power of two, fill the left space with one, this doesn't break the completeness and soundness
    let ones = vec![E::ScalarField::one(); domain_size - degree];
    f_evals.extend(ones.clone());
    g_evals.extend(ones.clone());

    // interpolate F(X) and G(X)
    let f = Evaluations::from_vec_and_domain(f_evals.clone(), domain).interpolate();
    let g = Evaluations::from_vec_and_domain(g_evals.clone(), domain).interpolate();

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

    // calculate the challenge, r, by hashing the commitments to F and G
    let mut transcript = Transcript::new();
    transcript.append_affines::<E>(&vec![
        cm_f.0, cm_g.0,
    ]);
    let r = transcript.append_and_digest::<E>("r".to_string());

    // compute the evaluations such that r - F(X) and r - G(X)
    let r_minus_f: Vec<_> = f_evals.iter().map(| eval | { r - eval }).collect();
    let r_minus_g: Vec<_> = g_evals.iter().map(| eval | { r - eval }).collect();

    // prove the product of r - F(X) is equal to r - G(X)
    let prod_check_proof = prod_check::prove(powers, &r_minus_f, &r_minus_g, domain, rng);

    let cm_r_minus_f = prod_check_proof.commitments[0][0];
    let cm_r_minus_g = prod_check_proof.commitments[0][1];
    let cm_t = prod_check_proof.commitments[0][2];
    let cm_q1 = prod_check_proof.commitments[0][3];
    let cm_q2 = prod_check_proof.commitments[0][4];

    // compute zeta
    let mut transcript = Transcript::new();
    transcript.append_affines::<E>(&vec![
        cm_r_minus_f.0, cm_r_minus_g.0, cm_t.0, cm_q1.0, cm_q2.0,
    ]);
    let zeta = transcript.append_and_digest::<E>("zeta".to_string());

    // open F(zeta) and G(zeta)
    let (h, open_evals, gamma) = batch_open(
        powers, 
        &vec![&f, &g], 
        &vec![&mask_f, &mask_g], 
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
            vec![cm_f, cm_g],
        ], 
        witnesses: prod_check_proof.witnesses.into_iter().chain(vec![h].into_iter()).collect(), 
        points: prod_check_proof.points.into_iter().chain(vec![zeta].into_iter()).collect(), 
        open_evals: prod_check_proof.open_evals.into_iter().chain(vec![open_evals].into_iter()).collect(), 
        gammas: prod_check_proof.gammas.into_iter().chain(vec![gamma].into_iter()).collect() 
    }
}

pub fn verify<E: Pairing, R: RngCore>(
    vk: &VerifierKey<E>,
    proof: &BatchCheckProof<E>,
    domain: Radix2EvaluationDomain<E::ScalarField>,
    rng: &mut R,
) {
    let cm_f = proof.commitments[3][0];
    let cm_g = proof.commitments[3][1];

    // compute the challenge, r
    let mut transcript = Transcript::new();
    transcript.append_affines::<E>(&vec![
        cm_f.0, cm_g.0,
    ]);
    let r = transcript.append_and_digest::<E>("r".to_string());

    let r_minus_f_zeta = &proof.open_evals[0][0].into_plain_value().0;
    let r_minus_g_zeta = &proof.open_evals[0][1].into_plain_value().0;
    let f_zeta = &proof.open_evals[3][0].into_plain_value().0;
    let g_zeta = &proof.open_evals[3][1].into_plain_value().0;

    // verify r - F(zeta) and r - G(zeta) are correct
    assert_eq!(r - f_zeta, *r_minus_f_zeta);
    assert_eq!(r - g_zeta, *r_minus_g_zeta);

    // perform the product check
    prod_check::verify(vk, proof, domain, domain.size(), rng);
}
