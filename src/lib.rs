mod types;
mod utils;
mod mult_check;
mod prod_check;
mod permutation_check;
mod prescribed_perm_check;
mod lookup_args;

#[cfg(test)]
mod tests {
    use ark_bls12_381::Bls12_381;
    use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
    use ark_poly_commit::kzg10::{Powers, VerifierKey, KZG10};
    use ark_std::{rand::{self, distributions::Uniform, Rng}, test_rng};
    use types::{BlsScalarField, UniPoly_381};

    use super::*;

    #[test]
    fn mult_check() {
        use mult_check::{prove, verify_evaluations, verify_product};

        let rng = &mut test_rng();

        // randomly generate test data
        let step = Uniform::new(1, u64::MAX);
        let values: Vec<_> = (0..9).into_iter()
            .map(| _ | {
                rng.sample(step)
            })
            .collect();

        // KZG trusted setup
        let degree = values.len();
        let max_degree = degree.checked_next_power_of_two().expect("length is too long");
        let pp = KZG10::<Bls12_381, UniPoly_381>::setup(max_degree, true, rng)
            .expect("KZG setup failed");
        let powers_of_g = pp.powers_of_g[..=max_degree].to_vec();
        let powers_of_gamma_g = (0..=max_degree).map(|i| pp.powers_of_gamma_g[&i]).collect();
        let powers: Powers<Bls12_381> = Powers {
            powers_of_g: ark_std::borrow::Cow::Owned(powers_of_g),
            powers_of_gamma_g: ark_std::borrow::Cow::Owned(powers_of_gamma_g),
        };

        // use the next power of two of the degree as the domain size
        let domain = Radix2EvaluationDomain::new(max_degree).expect("unsupported domain size");

        // generate the proof
        let proof = prove(&powers, &values, domain, rng);
        
        let vk = VerifierKey {
            g: pp.powers_of_g[0],
            gamma_g: pp.powers_of_gamma_g[&0],
            h: pp.h,
            beta_h: pp.beta_h,
            prepared_h: pp.prepared_h.clone(),
            prepared_beta_h: pp.prepared_beta_h.clone(),
        };

        // verify the product is correct
        verify_product(&values, &proof);

        // verify the evaluations are correct and polynomials are vanishing
        verify_evaluations(vk, &proof, domain, degree, rng);
    }

    #[test]
    fn prod_check() {
        use prod_check::{prove, verify};
        use rand::seq::SliceRandom;

        let rng = &mut test_rng();

        // randomly generate test data
        let step = Uniform::new(1, u64::MAX);
        let mut values: Vec<_> = (0..9).into_iter()
            .map(| _ | {
                BlsScalarField::from(rng.sample(step))
            })
            .collect();

        let f_evals = values.clone();
        values.shuffle(rng);
        let g_evals = values.clone();

        // KZG trusted setup
        let degree = f_evals.len();
        let next_power_of_two = degree.checked_next_power_of_two().expect("length is too long");
        let max_degree = next_power_of_two * 2;
        let pp = KZG10::<Bls12_381, UniPoly_381>::setup(max_degree, true, rng)
            .expect("KZG setup failed");
        let powers_of_g = pp.powers_of_g[..=max_degree].to_vec();
        let powers_of_gamma_g = (0..=max_degree).map(|i| pp.powers_of_gamma_g[&i]).collect();
        let powers: Powers<Bls12_381> = Powers {
            powers_of_g: ark_std::borrow::Cow::Owned(powers_of_g),
            powers_of_gamma_g: ark_std::borrow::Cow::Owned(powers_of_gamma_g),
        };

        // use the next power of two of the degree as the domain size
        let domain = Radix2EvaluationDomain::new(next_power_of_two).expect("unsupported domain size");

        let proof = prove(&powers, &f_evals, &g_evals, domain, rng);

        let vk = VerifierKey {
            g: pp.powers_of_g[0],
            gamma_g: pp.powers_of_gamma_g[&0],
            h: pp.h,
            beta_h: pp.beta_h,
            prepared_h: pp.prepared_h.clone(),
            prepared_beta_h: pp.prepared_beta_h.clone(),
        };

        verify(&vk, &proof, domain, degree, rng);
    }

    #[test]
    fn permutation_check() {
        use permutation_check::{prove, verify};
        use rand::seq::SliceRandom;

        let rng = &mut test_rng();

        // randomly generate test data
        let step = Uniform::new(1, u64::MAX);
        let mut values: Vec<_> = (0..9).into_iter()
            .map(| _ | {
                BlsScalarField::from(rng.sample(step))
            })
            .collect();

        let f_evals = values.clone();
        values.shuffle(rng);
        let g_evals = values.clone();

        // KZG trusted setup
        let degree = f_evals.len();
        let next_power_of_two = degree.checked_next_power_of_two().expect("length is too long");
        let max_degree = next_power_of_two * 2;
        let pp = KZG10::<Bls12_381, UniPoly_381>::setup(max_degree, true, rng)
            .expect("KZG setup failed");
        let powers_of_g = pp.powers_of_g[..=max_degree].to_vec();
        let powers_of_gamma_g = (0..=max_degree).map(|i| pp.powers_of_gamma_g[&i]).collect();
        let powers: Powers<Bls12_381> = Powers {
            powers_of_g: ark_std::borrow::Cow::Owned(powers_of_g),
            powers_of_gamma_g: ark_std::borrow::Cow::Owned(powers_of_gamma_g),
        };

        // use the next power of two of the degree as the domain size
        let domain = Radix2EvaluationDomain::new(next_power_of_two).expect("unsupported domain size");

        let proof = prove(&powers, &f_evals, &g_evals, domain, rng);

        let vk = VerifierKey {
            g: pp.powers_of_g[0],
            gamma_g: pp.powers_of_gamma_g[&0],
            h: pp.h,
            beta_h: pp.beta_h,
            prepared_h: pp.prepared_h.clone(),
            prepared_beta_h: pp.prepared_beta_h.clone(),
        };

        verify(&vk, &proof, domain, rng);
    }

    #[test]
    fn prescribed_perm_check() {
        use prescribed_perm_check::{prove, verify};
        use rand::seq::SliceRandom;

        let rng = &mut test_rng();

        // randomly generate test data
        let step = Uniform::new(1, u64::MAX);
        let values: Vec<_> = (0..9).into_iter()
            .map(| _ | {
                BlsScalarField::from(rng.sample(step))
            })
            .collect();

        let g_evals = values.clone();

        let mut s: Vec<_> = (0..9).into_iter().map(| val | { val }).collect();
        s.shuffle(rng);

        let mut f_evals = vec![];
        for i in s.clone() {
            f_evals.push(g_evals[i]);
        }

        // KZG trusted setup
        let degree = f_evals.len();
        let next_power_of_two = degree.checked_next_power_of_two().expect("length is too long");
        let max_degree = next_power_of_two * 2;
        let pp = KZG10::<Bls12_381, UniPoly_381>::setup(max_degree, true, rng)
            .expect("KZG setup failed");
        let powers_of_g = pp.powers_of_g[..=max_degree].to_vec();
        let powers_of_gamma_g = (0..=max_degree).map(|i| pp.powers_of_gamma_g[&i]).collect();
        let powers: Powers<Bls12_381> = Powers {
            powers_of_g: ark_std::borrow::Cow::Owned(powers_of_g),
            powers_of_gamma_g: ark_std::borrow::Cow::Owned(powers_of_gamma_g),
        };

        // use the next power of two of the degree as the domain size
        let domain = Radix2EvaluationDomain::new(next_power_of_two).expect("unsupported domain size");

        let s_evals = s.iter().map(| val | { domain.element(*val) }).collect();

        let proof = prove(&powers, &f_evals, &g_evals, &s_evals,domain, rng);

        let vk = VerifierKey {
            g: pp.powers_of_g[0],
            gamma_g: pp.powers_of_gamma_g[&0],
            h: pp.h,
            beta_h: pp.beta_h,
            prepared_h: pp.prepared_h.clone(),
            prepared_beta_h: pp.prepared_beta_h.clone(),
        };

        verify(vk, &proof, domain, rng);
    }

    #[test]
    fn lookup_args() {
        use lookup_args::{prove, verify};

        let rng = &mut test_rng();

        let a_evals = vec![2, 3, 5, 4, 2, 2, 5, 7];
        let s_evals = vec![1, 2, 3, 4, 5, 6, 7, 8];

        // KZG trusted setup
        let degree = a_evals.len();
        let next_power_of_two = degree.checked_next_power_of_two().expect("length is too long");
        let max_degree = next_power_of_two * 2;
        let pp = KZG10::<Bls12_381, UniPoly_381>::setup(max_degree, true, rng)
            .expect("KZG setup failed");
        let powers_of_g = pp.powers_of_g[..=max_degree].to_vec();
        let powers_of_gamma_g = (0..=max_degree).map(|i| pp.powers_of_gamma_g[&i]).collect();
        let powers: Powers<Bls12_381> = Powers {
            powers_of_g: ark_std::borrow::Cow::Owned(powers_of_g),
            powers_of_gamma_g: ark_std::borrow::Cow::Owned(powers_of_gamma_g),
        };

        // use the next power of two of the degree as the domain size
        let domain = Radix2EvaluationDomain::new(next_power_of_two).expect("unsupported domain size");

        let proofs = prove(&powers, &a_evals, &s_evals, domain, rng);

        let vk = VerifierKey {
            g: pp.powers_of_g[0],
            gamma_g: pp.powers_of_gamma_g[&0],
            h: pp.h,
            beta_h: pp.beta_h,
            prepared_h: pp.prepared_h.clone(),
            prepared_beta_h: pp.prepared_beta_h.clone(),
        };

        verify(&vk, &proofs, domain, rng);
    }
}
