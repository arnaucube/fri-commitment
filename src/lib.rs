#![allow(non_snake_case)]
#![allow(non_camel_case_types)]

pub mod merkletree;
use merkletree::{MerkleTreePoseidon as MT, Params as MTParams};

use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain, UVPolynomial,
};

use ark_std::log2;
use ark_std::marker::PhantomData;
use ark_std::ops::Mul;
use ark_std::{cfg_into_iter, rand::Rng, UniformRand};

pub struct FRI_LDT<F: PrimeField, P: UVPolynomial<F>> {
    _f: PhantomData<F>,
    _poly: PhantomData<P>,
}

impl<F: PrimeField, P: UVPolynomial<F>> FRI_LDT<F, P> {
    pub fn new() -> Self {
        Self {
            _f: PhantomData,
            _poly: PhantomData,
        }
    }

    pub fn split(p: &P) -> (P, P) {
        // let d = p.degree() + 1;
        let d = p.coeffs().len();
        if (d != 0) && (d & (d - 1) != 0) {
            println!("d={:?}", d);
            panic!("d should be a power of 2");
        }

        let coeffs = p.coeffs();
        let odd: Vec<F> = coeffs.iter().step_by(2).cloned().collect();
        let even: Vec<F> = coeffs.iter().skip(1).step_by(2).cloned().collect();

        return (
            P::from_coefficients_vec(odd),
            P::from_coefficients_vec(even),
        );
    }

    // prove implements the proof generation for a FRI-low-degree-testing
    pub fn prove<R: Rng>(rng: &mut R, p: &P) -> (Vec<F>, Vec<Vec<F>>, Vec<F>, [F; 2]) {
        let d = p.degree();
        let mut commitments: Vec<F> = Vec::new();
        let mut mts: Vec<MT<F>> = Vec::new();

        // f_0(x) = fL_0(x^2) + x fR_0(x^2)
        let mut f_i1 = p.clone();

        // sub_order = |F_i| = rho^-1 * d
        let mut sub_order = d; // TMP, TODO this will depend on rho parameter
        let mut eval_sub_domain: GeneralEvaluationDomain<F> =
            GeneralEvaluationDomain::new(sub_order).unwrap();

        // TODO merge in the next for loop
        let evals: Vec<F> = cfg_into_iter!(0..eval_sub_domain.size())
            .map(|k| f_i1.evaluate(&eval_sub_domain.element(k)))
            .collect();
        let (cm_i, mt_i) = MT::commit(&evals);
        commitments.push(cm_i);
        mts.push(mt_i);
        sub_order = sub_order / 2;
        eval_sub_domain = GeneralEvaluationDomain::new(sub_order).unwrap();
        //

        // V sets rand z \in \mathbb{F} challenge
        // TODO this will be a hash from the transcript
        let z_pos = 3;
        let z = eval_sub_domain.element(z_pos);
        let z_pos = z_pos * 2; // WIP

        let mut f_is: Vec<P> = Vec::new();
        f_is.push(p.clone());
        while f_i1.degree() > 1 {
            let alpha_i = F::from(42_u64); // TODO: WIP, defined by Verifier (well, hash transcript)

            let (fL_i, fR_i) = Self::split(&f_i1);

            // compute f_{i+1}(x) = fL_i(x) + alpha_i * fR_i(x)
            let aux = DensePolynomial::from_coefficients_slice(fR_i.coeffs());
            f_i1 = fL_i.clone() + P::from_coefficients_slice(aux.mul(alpha_i).coeffs());
            f_is.push(f_i1.clone());

            let subdomain_evaluations: Vec<F> = cfg_into_iter!(0..eval_sub_domain.size())
                .map(|k| f_i1.evaluate(&eval_sub_domain.element(k)))
                .collect();

            // commit to f_{i+1}(x) = fL_i(x) + alpha_i * fR_i(x)
            let (cm_i, mt_i) = MT::commit(&subdomain_evaluations); // commit to the evaluation domain instead
            commitments.push(cm_i);
            mts.push(mt_i);

            // prepare next subdomain
            sub_order = sub_order / 2;
            eval_sub_domain = GeneralEvaluationDomain::new(sub_order).unwrap();
        }
        let (fL_i, fR_i) = Self::split(&f_i1);
        let constant_fL_l: F = fL_i.coeffs()[0].clone();
        let constant_fR_l: F = fR_i.coeffs()[0].clone();

        // evals = {f_i(z^{2^i}), f_i(-z^{2^i})} \forall i \in F_i
        let mut evals: Vec<F> = Vec::new();
        let mut mtproofs: Vec<Vec<F>> = Vec::new();
        // TODO this will be done inside the prev loop, now it is here just for clarity
        // evaluate f_i(z^{2^i}), f_i(-z^{2^i}), and open their commitment
        for i in 0..f_is.len() {
            let z_2i = z.pow([2_u64.pow(i as u32)]); // z^{2^i} // TODO check usage of .pow(u64)
            let neg_z_2i = z_2i.neg();
            let eval_i = f_is[i].evaluate(&z_2i);
            evals.push(eval_i);
            let eval_i = f_is[i].evaluate(&neg_z_2i);
            evals.push(eval_i);

            // gen the openings in the commitment to f_i(z^(2^i))
            let mtproof = mts[i].open(F::from(z_pos as u32)); // WIP open to 2^i?
            mtproofs.push(mtproof);
        }

        (commitments, mtproofs, evals, [constant_fL_l, constant_fR_l])
    }

    // verify implements the verification of a FRI-low-degree-testing proof
    pub fn verify(
        degree: usize, // expected degree
        commitments: Vec<F>,
        mtproofs: Vec<Vec<F>>,
        evals: Vec<F>,
        constants: [F; 2],
    ) -> bool {
        let sub_order = ((degree + 1) / 2) - 1; // TMP, TODO this will depend on rho parameter
        let eval_sub_domain: GeneralEvaluationDomain<F> =
            GeneralEvaluationDomain::new(sub_order).unwrap();
        // TODO this will be a hash from the transcript
        let z_pos = 3;
        let z = eval_sub_domain.element(z_pos);
        let z_pos = z_pos * 2;

        if commitments.len() != (evals.len() / 2) {
            println!("sho commitments.len() != (evals.len() / 2) - 1");
            return false;
        }

        let mut i_z = 0;
        for i in (0..evals.len()).step_by(2) {
            let alpha_i = F::from(42_u64); // TODO: WIP, defined by Verifier (well, hash transcript)

            // take f_i(z^2) from evals
            let z_2i = z.pow([2_u64.pow(i_z as u32)]); // z^{2^i}
            let fi_z = evals[i];
            let neg_fi_z = evals[i + 1];
            // compute f_i^L(z^2), f_i^R(z^2) from the linear combination
            let L = (fi_z + neg_fi_z) * F::from(2_u32).inverse().unwrap();
            let R = (fi_z - neg_fi_z) * (F::from(2_u32) * z_2i).inverse().unwrap();

            // compute f_{i+1}(z^2) = f_i^L(z^2) + a_i f_i^R(z^2)
            let next_fi_z2 = L + alpha_i * R;

            // check: obtained f_{i+1}(z^2) == evals.f_{i+1}(z^2) (=evals[i+2])
            if i < evals.len() - 2 {
                if next_fi_z2 != evals[i + 2] {
                    println!(
                        "verify step i={}, should f_i+1(z^2) == evals.f_i+1(z^2) (=evals[i+2])",
                        i
                    );
                    return false;
                }
            }

            // check commitment opening
            if !MT::verify(
                commitments[i_z],
                // F::from(i as u32),
                F::from(z_pos as u32),
                evals[i],
                mtproofs[i_z].clone(),
            ) {
                println!("verify step i={}, MT::verify failed", i);
                return false;
            }

            // last iteration, check constant values equal to the obtained f_i^L(z^{2^i}),
            // f_i^R(z^{2^i})
            if i == evals.len() - 2 {
                if L != constants[0] {
                    println!("constant L not equal to the obtained one");
                    return false;
                }
                if R != constants[1] {
                    println!("constant R not equal to the obtained one");
                    return false;
                }
            }
            i_z += 1;
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::Field;
    use ark_std::UniformRand;
    pub type Fr = ark_bn254::Fr; // scalar field
    use ark_poly::univariate::DensePolynomial;
    use ark_poly::Polynomial;

    #[test]
    fn test_split() {
        let mut rng = ark_std::test_rng();
        let deg = 7;
        let p = DensePolynomial::<Fr>::rand(deg, &mut rng);
        assert_eq!(p.degree(), deg);

        type FRIT = FRI_LDT<Fr, DensePolynomial<Fr>>;
        let (pL, pR) = FRIT::split(&p);

        // check that f(z) == fL(x^2) + x * fR(x^2), for a rand z
        let z = Fr::rand(&mut rng);
        assert_eq!(
            p.evaluate(&z),
            pL.evaluate(&z.square()) + z * pR.evaluate(&z.square())
        );
    }

    #[test]
    fn test_prove() {
        let mut rng = ark_std::test_rng();

        let deg = 15;
        let p = DensePolynomial::<Fr>::rand(deg, &mut rng);
        assert_eq!(p.degree(), deg);
        // println!("p {:?}", p);

        type FRIT = FRI_LDT<Fr, DensePolynomial<Fr>>;
        // prover
        let (commitments, mtproofs, evals, constvals) = FRIT::prove(&mut rng, &p);
        // commitments contains the commitments to each f_0, f_1, ..., f_n, with n=log2(d)
        assert_eq!(commitments.len(), log2(p.coeffs().len()) as usize);
        assert_eq!(evals.len(), 2 * log2(p.coeffs().len()) as usize);

        let v = FRIT::verify(
            // Fr::from(deg as u32),
            deg,
            commitments,
            mtproofs,
            evals,
            constvals,
        );
        assert!(v);
    }
}
