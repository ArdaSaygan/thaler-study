use ark_ff::fields::{MontBackend, MontConfig};
use ark_ff::Fp64;

use ark_poly::multivariate::{SparsePolynomial, SparseTerm, Term};
use ark_poly::DenseMVPolynomial;

use sum_check_protocol::SumCheckPolynomial;

use sha2::{Sha256, Digest};

use sum_check_protocol::{NoninteractiveProver, NoninteractiveVerifier};

#[derive(MontConfig)]
#[modulus = "5"]
#[generator = "2"]
struct FrConfig;
type Fp5 = Fp64<MontBackend<FrConfig, 1>>;

fn main() {
    println!("Using Fp5");

    let a = Fp5::from(2);
    let b = Fp5::from(3);
    let c = a + b;
    println!("{:?} + {:?} = {:?}", a,b,c);

    // p = 2*x_0^3 + x_0*x_1 + 3*x_1^2
    let p = SparsePolynomial::from_coefficients_vec(
        2, // Number of variables
        vec![
            (Fp5::from(2), SparseTerm::new(vec![(0,3)])),
            (Fp5::from(1), SparseTerm::new(vec![(0,1), (1,1)])),
            (Fp5::from(3), SparseTerm::new(vec![(1,2)]))
        ]
    );

    println!("p(x0, x1) = {:?}", p);

    println!("p(2,3) = {:?}", SumCheckPolynomial::evaluate(&p,&vec![Fp5::from(2),Fp5::from(3)]).unwrap());

    let fixed_p = p.fix_variables(&[Fp5::from(2)]);
    println!("p(2,x0) = {:?}", fixed_p);


    println!("SHA of 15 = {:?}", Sha256::digest(&15u64.to_le_bytes()));


    println!("\n\n>>> PROVING TIME <<<\n\n");
    let mut prover = NoninteractiveProver::new(p.clone());
    let proof = prover.generate_proof();
    println!("Proof: {:?}", proof);

    println!("\n\n>>> Verification TIME <<<\n\n");
    let c1 = p.to_evaluations().into_iter().sum();
    let verifier = NoninteractiveVerifier::new(p, c1);
    let result = verifier.verify(proof);
    println!("Verification result: {:?}", result);

}