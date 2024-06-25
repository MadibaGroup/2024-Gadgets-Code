use std::collections::BTreeMap;
use std::ops::Mul;

use ark_ec::pairing::Pairing;
use ark_poly::{univariate::{DenseOrSparsePolynomial, DensePolynomial}, DenseUVPolynomial, EvaluationDomain, Evaluations, Polynomial, Radix2EvaluationDomain};
use ark_poly_commit::kzg10::{Powers, VerifierKey, KZG10};
use ark_std::{iterable::Iterable, rand::RngCore, Zero, One};

use crate::{permutation_check, utils::{batch_check, batch_open, calculate_hash, BatchCheckProof, HashBox}};

/// [unoptimized] the lookup argument in halo2
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

    // calculate the challenge, xi
    let xi = calculate_hash(
        &vec![
                HashBox::<E>{ object: cm_a_prime.0 },
                HashBox::<E>{ object: cm_s_prime.0 },
                HashBox::<E>{ object: cm_q1.0 },
                HashBox::<E>{ object: cm_q2.0 },
            ]
        );

    // open the evaluations at xi for A', S', Q1 and Q2
    let (h1, open_evals1, gamma1) = batch_open(
        powers, 
        &vec![&a_prime, &s_prime, &q1, &q2], 
        &vec![&mask_a_prime, &mask_s_prime, &mask_q1, &mask_q2], 
        xi, 
        false, 
        rng
    );

    let omega = domain.element(1);

    // open the evaluation at xi*omega for A'
    let (h2, open_evals2, gamma2) = batch_open(
        powers, 
        &vec![&a_prime], 
        &vec![&mask_a_prime], 
        xi / omega, 
        false, 
        rng
    );

    let proof = BatchCheckProof {
        commitments: vec![
            vec![cm_a_prime, cm_s_prime, cm_q1, cm_q2],
            vec![cm_a_prime],
        ],
        witnesses: vec![h1, h2],
        points: vec![xi, xi / omega],
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

    // verify xi is correct
    let xi = calculate_hash(
            &vec![
                HashBox::<E>{ object: cm_a_prime.0 },
                HashBox::<E>{ object: cm_s_prime.0 },
                HashBox::<E>{ object: cm_q1.0 },
                HashBox::<E>{ object: cm_q2.0 },
            ]
        );
    assert_eq!(xi, proof.points[0]);

    // verify xi*omega is correct
    let omega = domain.element(1);
    assert_eq!(xi / omega, proof.points[1]);

    // read the evaluations of A'(xi), S'(xi), Q1(xi), A'(xi*omega)
    let a_prime_xi = &proof.open_evals[0][0].into_plain_value().0;
    let s_prime_xi = &proof.open_evals[0][1].into_plain_value().0;
    let q1_xi = &proof.open_evals[0][2].into_plain_value().0;
    let a_prime_xi_omega = &proof.open_evals[1][0].into_plain_value().0;

    // evaluate Z(X) at xi
    let z = domain.vanishing_polynomial();
    let z_xi = z.evaluate(&xi);

    // verify [A'(X) - A'(X/w)] * [A'(X) - S'(X)] = Z(X) * Q1(X)
    let lhs = (*a_prime_xi - a_prime_xi_omega).mul(*a_prime_xi - s_prime_xi);
    let rhs = z_xi.mul(q1_xi);
    assert_eq!(lhs, rhs);

    let q2_xi = &proof.open_evals[0][3].into_plain_value().0;

    // verify L0(X) * [A'(X) - S'(X)] = Z(X) * Q2(X)
    let x_minus_one = DenseOrSparsePolynomial::from(DensePolynomial::from_coefficients_vec(vec![-E::ScalarField::one(), E::ScalarField::one()]));
    let (l0, _) = DenseOrSparsePolynomial::from(z).divide_with_q_and_r(&x_minus_one).unwrap();
    let l0_xi = l0.evaluate(&xi);
    let lhs = l0_xi.mul(*a_prime_xi - s_prime_xi);
    let rhs = z_xi.mul(q2_xi);
    assert_eq!(lhs, rhs);

    batch_check(vk, proof, rng);
    
    for i in 1..proofs.len() {
        let proof = &proofs[i];
        permutation_check::verify(vk, proof, domain, rng);
    }
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
