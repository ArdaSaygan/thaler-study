use std::marker::PhantomData;

use ark_ff::{Field, Zero, PrimeField, BigInteger};
use ark_ff::field_hashers::{DefaultFieldHasher, HashToField};
use ark_poly::{
    multivariate::{self, SparseTerm, Term},
    polynomial::DenseMVPolynomial,
    univariate, Polynomial,
};
use ark_std::rand::Rng;
use bitvec::slice::BitSlice;

use sha2::{Digest, Sha256};


pub trait RngF<F> {
    fn draw(&mut self) -> F;
}

impl<F: Field, T: Rng> RngF<F> for T {
    fn draw(&mut self) -> F {
        F::rand(self)
    }
}

/// An error type of sum check protocol
#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("prover claim mismatches evaluation {0} {1}")]
    ProverClaimMismatch(String, String),

    #[error("verifier has no oracle access to the polynomial")]
    NoPolySet,
}

/// A convenient way to iterate over $n$-dimentional boolean hypercube.
pub struct BooleanHypercube<F: Field> {
    n: u32,
    current: u64,
    __f: PhantomData<F>,
}

impl<F: Field> BooleanHypercube<F> {
    /// Create an $n$-dimentional [`BooleanHypercube`]
    pub fn new(n: u32) -> Self {
        Self {
            n,
            current: 0,
            __f: PhantomData,
        }
    }
}

impl<F: Field> Iterator for BooleanHypercube<F> {
    type Item = Vec<F>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current == 2u64.pow(self.n) {
            None
        } else {
            let vec = self.current.to_le_bytes();
            let s: &BitSlice<u8> = BitSlice::try_from_slice(&vec).unwrap();
            self.current += 1;

            Some(
                s.iter()
                    .take(self.n as usize)
                    .map(|f| match *f {
                        false => F::zero(),
                        true => F::one(),
                    })
                    .collect(),
            )
        }
    }
}

/// The state of the Prover.
pub struct Prover<F: Field, P: SumCheckPolynomial<F>> {
    /// $g$ a polynomial being used in this run of the protocol.
    g: P,

    /// $C_1$ a value prover _claims_ equal the true answer.
    c_1: F,

    /// Random values $r_1,...,r_j$ sent by the [`Verifier`] in the
    /// previous rounds.
    r: Vec<F>,
    num_vars: usize,
}

impl<F: Field, P: SumCheckPolynomial<F>> Prover<F, P> {
    /// Create a new [`Prover`] state with the polynomial $g$.
    pub fn new(g: P) -> Self {
        let c_1 = g.to_evaluations().into_iter().sum();
        let num_vars = g.num_vars();
        Self {
            g,
            c_1,
            num_vars,
            r: Vec::with_capacity(num_vars),
        }
    }

    /// Get the value $C_1$ that prover claims equal true answer.
    pub fn c_1(&self) -> F {
        self.c_1
    }

    /// Perform $j$-th round of the [`Prover`] side of the prococol.
    pub fn round(&mut self, r_prev: F, j: usize) -> univariate::SparsePolynomial<F> {
        if j != 0 {
            self.r.push(r_prev);
            self.g = self.g.fix_variables(&[r_prev]);
        }

        self.g.to_univariate()
    }

    pub fn num_vars(&self) -> usize {
        self.num_vars
    }
}

/// An abstraction over all types of polynomials that may be
/// used in a sumcheck protocol.
pub trait SumCheckPolynomial<F: Field> {
    /// Evaluates `self` at a given point
    ///
    /// Return `None` if dimentionality of `point` does not match
    /// an expected one.
    fn evaluate(&self, point: &[F]) -> Option<F>;

    /// Reduce the number of variables in `Self` by fixing a
    /// `partial_point.len()` variables at `partial_point`.
    fn fix_variables(&self, partial_point: &[F]) -> Self;

    /// Compute the $j$-th round of polynomial for sumcheck over
    /// first variable.
    ///
    /// Reduces to univariate polynomial of first variable:
    ///
    /// $$
    /// \sum_{(x_{j+1},\cdots,x_{\nu}) \in \lbrace 0, 1 \rbrace ^{\nu - 1}}
    /// g(X_j,x_{j+1},x_{j+2},\cdots,x_{\nu})
    /// $$
    ///
    /// Note that the initial polynomial $g(x_1,\cdots,x_{\nu})$ that
    /// the protocol was started with is supposed to become
    /// $g(r_1,r_2,\cdots,x_j,\cdots,x_n)$ at this point by calling [`fix_variables`]
    ///
    ///
    /// [`fix_variables`]: SumCheckPolynomial::fix_variables
    fn to_univariate(&self) -> univariate::SparsePolynomial<F>;

    /// Returns the number of variables in `self`
    fn num_vars(&self) -> usize;

    /// Returns a list of evaluations over the domain, which is the
    /// boolean hypercube.
    fn to_evaluations(&self) -> Vec<F>;
}

impl<F: Field> SumCheckPolynomial<F> for multivariate::SparsePolynomial<F, SparseTerm> {
    fn evaluate(&self, point: &[F]) -> Option<F> {
        Some(Polynomial::evaluate(self, &point.to_owned()))
    }

    fn fix_variables(&self, partial_point: &[F]) -> Self {
        let mut res = Self::zero();
        let num_vars = DenseMVPolynomial::num_vars(self);
        let mut full_point = partial_point.to_vec();
        full_point.append(&mut vec![F::one(); num_vars - partial_point.len()]);

        for (coeff, term) in self.terms() {
            let mut eval = term.evaluate(&full_point);
            eval *= coeff;
            let new_term = SparseTerm::new(
                term.iter()
                    .filter(|(var, _)| *var >= partial_point.len())
                    .map(|(var, power)| (var - partial_point.len(), *power))
                    .collect(),
            );
            let poly = multivariate::SparsePolynomial {
                num_vars: num_vars - partial_point.len(),
                terms: vec![(eval, new_term)],
            };

            res += &poly;
        }

        res
    }

    fn to_univariate(&self) -> univariate::SparsePolynomial<F> {
        let mut res = univariate::SparsePolynomial::zero();

        for p in BooleanHypercube::new((DenseMVPolynomial::num_vars(self) - 1) as u32) {
            let mut point = vec![F::one()];
            point.extend_from_slice(&p);
            let mut r = univariate::SparsePolynomial::zero();

            for (coeff, term) in self.terms() {
                let mut eval = term.evaluate(&point);
                let power = term
                    .iter()
                    .find(|(variable, _power)| *variable == 0)
                    .map(|(_variable, power)| *power)
                    .unwrap_or(0);

                eval *= coeff;

                r += &univariate::SparsePolynomial::from_coefficients_slice(&[(power, eval)]);
            }
            res += &r;
        }

        res
    }

    fn num_vars(&self) -> usize {
        DenseMVPolynomial::num_vars(self)
    }

    fn to_evaluations(&self) -> Vec<F> {
        BooleanHypercube::new(DenseMVPolynomial::num_vars(self) as u32)
            .map(|point| Polynomial::evaluate(self, &point))
            .collect()
    }
}

/// The state of the Verifier.
pub struct Verifier<F: Field, P: SumCheckPolynomial<F>> {
    /// Number of variables in the original polynomial.
    n: usize,

    /// A $C_1$ value claimed by the Prover.
    c_1: F,

    /// Univariate polynomials $g_1,...,g_{j-1}$ received from the [`Prover`].
    g_part: Vec<univariate::SparsePolynomial<F>>,

    /// Previously picked random values $r_1,...,r_{j-1}$.
    r: Vec<F>,

    /// Original polynomial for oracle access
    g: Option<P>,
}

/// Values returned by Validator as a result of its run on every step.
#[derive(Debug)]
pub enum VerifierRoundResult<F: Field> {
    /// On $j$-th round the verifier outputs a random $r_j$ value
    JthRound(F),

    /// On final round the verifier outputs `true` or `false` if it accepts
    /// or rejects the proof.
    FinalRound(bool),
}

impl<F: Field, P: SumCheckPolynomial<F>> Verifier<F, P> {
    /// Create the new state of the [`Verifier`].
    ///
    /// $n$ - degree of the polynomial
    /// $C_1$ - the value claimed to be true answer by the [`Prover`].
    /// $g$ - the polynimial itself for oracle access by the [`Verifier`].
    pub fn new(n: usize, g: Option<P>) -> Self {
        Self {
            n,
            c_1: F::zero(),
            g_part: Vec::with_capacity(n),
            r: Vec::with_capacity(n),
            g,
        }
    }

    pub fn set_c_1(&mut self, c_1: F) {
        self.c_1 = c_1;
    }

    /// Perform the $j$-th round of the [`Verifier`] side of the protocol.
    ///
    /// $g_j$ - a univariate polynomial sent in this round by the [`Prover`].
    pub fn round<R: RngF<F>>(
        &mut self,
        g_j: univariate::SparsePolynomial<F>,
        rng: &mut R,
    ) -> Result<VerifierRoundResult<F>, Error> {
        let r_j = rng.draw();
        if self.r.is_empty() {
            // First Round
            let evaluation = g_j.evaluate(&F::zero()) + g_j.evaluate(&F::one());
            if self.c_1 != evaluation {
                Err(Error::ProverClaimMismatch(
                    format!("start {:?}", self.c_1),
                    format!("{:?}", evaluation),
                ))
            } else {
                self.g_part.push(g_j);
                self.r.push(r_j);

                Ok(VerifierRoundResult::JthRound(r_j))
            }
        } else if self.r.len() == (self.n - 1) {
            // Last round
            self.r.push(r_j);

            if let Some(g) = &self.g {
                assert_eq!(g_j.evaluate(&r_j), g.evaluate(&self.r).unwrap());

                Ok(VerifierRoundResult::FinalRound(
                    g_j.evaluate(&r_j) == g.evaluate(&self.r).unwrap(),
                ))
            } else {
                Err(Error::NoPolySet)
            }
        } else {
            // j-th round
            let g_jprev = self.g_part.last().unwrap();
            let r_jprev = self.r.last().unwrap();

            let prev_evaluation = g_jprev.evaluate(r_jprev);
            let evaluation = g_j.evaluate(&F::zero()) + g_j.evaluate(&F::one());
            if prev_evaluation != evaluation {
                return Err(Error::ProverClaimMismatch(
                    format!("{:?}", prev_evaluation),
                    format!("{:?}", evaluation),
                ));
            }

            self.g_part.push(g_j);
            self.r.push(r_j);

            Ok(VerifierRoundResult::JthRound(r_j))
        }
    }
}






/// Random Oracle access to retrieve r_i = H(c_i || r_{i-1})
pub fn random_oracle<F:PrimeField>(c_i : F, r_im1 : Option<F>) -> F {
    let mut hasher = Sha256::new();
    let to_field_hasher = <DefaultFieldHasher<Sha256> as HashToField<F>>::new(&[]);

    hasher.update(c_i.into_bigint().to_bytes_be());  // TODO: Replace c_{i-1} with g_{i-1}
    if r_im1.is_some() {
        hasher.update(r_im1.unwrap().into_bigint().to_bytes_be());
    }
    let hash = hasher.finalize();
    let r_i = to_field_hasher.hash_to_field::<1>(&hash)[0];
    r_i
}


// Applying Fiat-Shamir to the protocol
pub struct NoninteractiveProver<F: Field, P: SumCheckPolynomial<F>> {
    /// polynomials $g, g_1,...,g_k$
    /// where g is the original polynomial for which \sum g(x_i) = c_1
    /// and $g_i = g(r1, r2, ..., ri, ..., x_k)$ 
    gs: Vec<P>,

    /// sums $c_1, c_2, ..., c_{k+1}$
    /// 
    cs : Vec<F>,

    /// s_i polynomials, sent by the Prover
    /// where $s_1(0)+s_1(1) = c_1$ and $s_i(0)+s_i(1) = \sum g_{i-1}$
    sis: Vec<univariate::SparsePolynomial<F>>,

    /// Random values $r_1,...,r_{k-1}$ returned from the Random Oracle
    rs: Vec<F>,

    /// k
    num_vars: usize,

    /// shows how many rounds are done
    round: usize,
}

pub type Proof<F> = (Vec<univariate::SparsePolynomial<F>>, Vec<F>);

impl<F: PrimeField, P: SumCheckPolynomial<F> + std::fmt::Debug> NoninteractiveProver<F, P>{
    /// Create a new [`NoninteractiveProver`] state with the polynomial $g$.
    pub fn new(g: P) -> Self {
        let c_1 = g.to_evaluations().into_iter().sum();
        let s_1 = g.to_univariate();
        let num_vars = g.num_vars();
        Self {
            gs: vec![g],
            cs: vec![c_1],
            sis: vec![s_1],
            rs: Vec::with_capacity(num_vars),
            num_vars,
            round: 0,
        }
    }

    /// Run the Prover side of the protocol for round i
    pub fn round(&mut self) {
        if self.round > self.num_vars{
            panic!("Already finished the protocol");
        }

        // Get the random value from the Random Oracle
        // Ideally,
        // r_i = H(g || c_1 || g_1 || r_2 || g_2 || ... || r_{i-1} || g_{i})
        // For simplicity, we will use
        // r_i = H(r_{i-1} || c_{i-1})
        let r_i = random_oracle(*self.cs.last().unwrap(), self.rs.last().copied());
        
        // Get g_{i}
        let g_im1 = self.gs.last().unwrap();
        let g_i = g_im1.fix_variables(&[r_i]);

        // Get s_i = \sum g_i
        let s_i = g_i.to_univariate();

        // Get c_{i} = s_i(0) + s_i(1)
        let c_i = s_i.evaluate(&F::zero()) + s_i.evaluate(&F::one());

        // update the state
        self.gs.push(g_i);
        self.cs.push(c_i);
        self.rs.push(r_i);
        if self.round < self.num_vars - 1 { // if it's the last round, there are no s_i to send to verifier
            self.sis.push(s_i);
        }
        
        self.round += 1;
    }
    
    pub fn generate_proof(&mut self) -> Proof<F> {
        println!("Generating proof for polynomial {:?}", self.gs[0]);
        println!("Claimed value: {:?}", self.cs[0]);
        println!("Number of variables: {:?}", self.num_vars);

        for _i in 0..self.num_vars {
            self.round();
        }

        (self.sis.clone(), self.rs.clone())
    }

    pub fn c_1(&self) -> F {
        self.cs[0]
    }
}

pub struct NoninteractiveVerifier<F: Field, P: SumCheckPolynomial<F>> {
    /// Number of variables k in the original polynomial.
    num_vars: usize,

    /// Polynomial $g$ for which the proof is generated
    g: P,

    /// A $C_1$ value claimed by the Prover.
    c_1: F,
}

impl<F: PrimeField, P: SumCheckPolynomial<F> + std::fmt::Debug> NoninteractiveVerifier<F, P> {

    pub fn new(g:P, c_1:F) -> Self {
        Self {
            num_vars: g.num_vars(),
            g,
            c_1,
        }
    }

    pub fn verify(&self, proof: Proof<F>) -> bool {
        let (sis, rs) = proof;
        if sis.len() != self.num_vars || rs.len() != self.num_vars {
            panic!("Proof is not valid, number of s_i (and r_i) should be equal to number of variables");
        }

        // Base case, 
        if sis[0].evaluate(&F::zero()) + sis[0].evaluate(&F::one()) != self.c_1 {
            println!("Proof is not valid, s_1(0) + s_1(1) != c_1");
            return false;
        }
        let r_1 = random_oracle(self.c_1, None);
        println!("r_1 = H(c_1 || None), {} = H({}||None)", r_1, self.c_1);
        if r_1 != rs[0] {
            println!("Proof is not valid, r_1 != H(c_1)");
            return false;
        }

        // Recursive Case
        let mut c_i = sis[0].evaluate(&r_1);
        for i in 1..self.num_vars{

            // Is the random value r_i from the Random Oracle correct?
            // r_i = H(c_i || r_{i-1}) ?
            if rs[i] != random_oracle(c_i, Some(rs[i-1])){
                println!("Proof is not valid, r_{} != H(c_{}, r_{})", i+1, i+1 , i);
                return false;
            }

            // Is the polynomial s_i correct?
            if sis[i].evaluate(&F::zero()) + sis[i].evaluate(&F::one()) != c_i {
                println!("Proof is not valid, s_{}(0) + s_{}(1) != c_{}", i+1,i+1,i+1);
                return false;
            }

            // Update c_i to c_{i+1}
            c_i = sis[i].evaluate(&rs[i]);
        }

        // Check if g(r1,r2,...,r_k) == c_{k+1}
        if c_i != self.g.evaluate(&rs).unwrap() {
            println!("Proof is not valid, c_{} != g(r_1,r_2,...,r_k)", self.num_vars+1);
            return false;
        }

        true
    }


}


































#[cfg(test)]
mod tests {
    use ark_ff::{
        fields::Fp64,
        fields::{MontBackend, MontConfig},
        Field, One, PrimeField,
    };
    use ark_poly::{
        multivariate::{self, SparseTerm, Term},
        DenseMVPolynomial,
    };
    use ark_std::{rand::Rng, test_rng};
    use pretty_assertions::assert_eq;

    use crate::{Prover, SumCheckPolynomial, Verifier, VerifierRoundResult, NoninteractiveProver, NoninteractiveVerifier};

    #[derive(MontConfig)]
    #[modulus = "5"]
    #[generator = "2"]
    struct FrConfig;

    type Fp5 = Fp64<MontBackend<FrConfig, 1>>;

    /// Generate random `l`-variate polynomial of maximum individual degree `d`
    fn rand_poly<R: Rng, F: Field>(
        l: usize,
        d: usize,
        rng: &mut R,
    ) -> multivariate::SparsePolynomial<F, SparseTerm> {
        let mut random_terms = Vec::new();
        let num_terms = rng.gen_range(1..1000);
        // For each term, randomly select up to `l` variables with degree
        // in [1,d] and random coefficient
        random_terms.push((F::rand(rng), SparseTerm::new(vec![])));
        for _ in 1..num_terms {
            let term = (0..l)
                .filter_map(|i| {
                    if rng.gen_bool(0.5) {
                        Some((i, rng.gen_range(1..(d + 1))))
                    } else {
                        None
                    }
                })
                .collect();
            let coeff = F::rand(rng);
            random_terms.push((coeff, SparseTerm::new(term)));
        }
        multivariate::SparsePolynomial::from_coefficients_slice(l, &random_terms)
    }

    #[test]
    fn basic_test() {
        // 2 * x_1 * x_2 + 3 * x_1^2 * x_2^2
        let poly = multivariate::SparsePolynomial::from_coefficients_slice(
            2,
            &[
                (
                    Fp5::from_bigint(2u32.into()).unwrap(),
                    multivariate::SparseTerm::new(vec![(0, 1), (1, 1)]),
                ),
                (
                    Fp5::from_bigint(3u32.into()).unwrap(),
                    multivariate::SparseTerm::new(vec![(0, 2), (1, 2)]),
                ),
            ],
        );

        let res = poly.fix_variables(&[2u32.into()]);

        let poly_expected = multivariate::SparsePolynomial::from_coefficients_slice(
            1,
            &[
                (
                    Fp5::from_bigint(4u32.into()).unwrap(),
                    multivariate::SparseTerm::new(vec![(0, 1)]),
                ),
                (
                    Fp5::from_bigint(2u32.into()).unwrap(),
                    multivariate::SparseTerm::new(vec![(0, 2)]),
                ),
            ],
        );
        assert_eq!(res, poly_expected);
    }

    #[test]
    fn test_from_book() {
        let rng = &mut test_rng();
        // 2 *x_1^3 + x_1 * x_3 + x_2 * x_3
        let g = multivariate::SparsePolynomial::from_coefficients_slice(
            3,
            &[
                (
                    Fp5::from_bigint(2u32.into()).unwrap(),
                    multivariate::SparseTerm::new(vec![(0, 3)]),
                ),
                (
                    Fp5::from_bigint(1u32.into()).unwrap(),
                    multivariate::SparseTerm::new(vec![(0, 1), (2, 1)]),
                ),
                (
                    Fp5::from_bigint(1u32.into()).unwrap(),
                    multivariate::SparseTerm::new(vec![(1, 1), (2, 1)]),
                ),
            ],
        );

        let mut prover = Prover::new(g.clone());
        let c_1 = prover.c_1();
        let mut r_j = Fp5::one();
        let mut verifier = Verifier::new(3, Some(g));
        verifier.set_c_1(c_1);

        for j in 0..3 {
            let g_j = prover.round(r_j, j);
            let verifier_res = verifier.round(g_j, rng).unwrap();
            match verifier_res {
                VerifierRoundResult::JthRound(r) => {
                    r_j = r;
                }
                VerifierRoundResult::FinalRound(res) => {
                    assert!(res);
                    break;
                }
            }
        }
    }
    
    #[test]
    fn randomized_test() {
        /*
        let rng = &mut test_rng();

        for var_count in 1..10 {
            let degree = 10;
            let poly: multivariate::SparsePolynomial<Fp5, SparseTerm> =
                rand_poly(var_count, degree, rng);

            let mut point = Vec::with_capacity(var_count);

            for _ in 0..var_count {
                point.push(Fp5::rand(rng));
            }

            let normal_evaluation = Polynomial::evaluate(&poly, &point);

            for fixed_var_idx in 0..var_count {
                let reduced_uni_poly = poly.to_univariate_at_point(fixed_var_idx, &point).unwrap();

                let univariate_evaluation = reduced_uni_poly.evaluate(&point[fixed_var_idx]);

                assert_eq!(
                    normal_evaluation, univariate_evaluation,
                    "{:?} \n\n {:?}",
                    poly, reduced_uni_poly
                );
            }
        }
        */
    }

    #[test]
    fn protocol_test() {
        for n in 2..10 {
            let rng = &mut test_rng();

            let g = rand_poly(n, 3, rng);

            let mut prover = Prover::new(g.clone());
            let c_1 = prover.c_1();
            let mut r_j = Fp5::one();
            let mut verifier = Verifier::new(n, Some(g));
            verifier.set_c_1(c_1);

            for j in 0..n {
                let g_j = prover.round(r_j, j);
                let verifier_res = verifier.round(g_j, rng).unwrap();
                match verifier_res {
                    VerifierRoundResult::JthRound(r) => {
                        r_j = r;
                    }
                    VerifierRoundResult::FinalRound(res) => {
                        assert!(res);
                        break;
                    }
                }
            }
        }
    }

    #[test]
    fn noninteractive_protocol_test() {
        for n in 2..10 {
            let rng = &mut test_rng();

            let g = rand_poly(n, 3, rng);

            let mut prover = NoninteractiveProver::new(g.clone());
            let c_1 : Fp5 = prover.c_1();
            let proof = prover.generate_proof();

            let verifier = NoninteractiveVerifier::new(g.clone(), c_1);
            let res = verifier.verify(proof);
            assert!(res);
        }
    }

    #[test]
    fn noninteractive_soundness_test() {
        for n in 2..10 {
            let rng = &mut test_rng();

            let g = rand_poly(n, 3, rng);

            let mut prover = NoninteractiveProver::new(g.clone());
            let c_1 : Fp5 = prover.c_1();
            let proof = prover.generate_proof();

            let verifier = NoninteractiveVerifier::new(g.clone(), c_1+Fp5::one());
            let res = verifier.verify(proof);
            assert!(res == false);
        }
    }
}
