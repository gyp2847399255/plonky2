use core::marker::PhantomData;

use anyhow::Result;
use plonky2::field::types::{PrimeField, Sample};
use plonky2::iop::witness::{PartialWitness, PartitionWitness, Witness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData, CommonCircuitData};
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig, PoseidonGoldilocksConfig};

/// An example of using Plonky2 to prove a statement of the form
/// "I know the square root of this field element."
fn main() -> Result<()> {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let config = CircuitConfig::standard_recursion_config();

    let mut builder = CircuitBuilder::<F, D>::new(config);

    let x = builder.add_virtual_target();

    let x_squared = builder.mul(x, x);
    builder.register_public_input(x_squared);

    // Randomly generate the value of x^2: any quadratic residue in the field works.
    let (x_value, x_squared_value) = {
        let val = F::rand();
        println!("{}", val * val);
        (val, val * val)
    };

    let mut pw = PartialWitness::new();
    pw.set_target(x, x_value);
    pw.set_target(x_squared, x_squared_value);

    let data = builder.build::<C>();
    let proof = data.prove(pw.clone())?;

    let x_squared_actual = proof.public_inputs[0];
    println!("Field element (square): {x_squared_actual}");

    data.verify(proof)
}
