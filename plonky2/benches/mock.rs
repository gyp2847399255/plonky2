use std::time::Instant;

use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use plonky2_field::types::Sample;

fn main() {
    bench_mock_circuit(26, 1);
}

fn bench_mock_circuit(nv: usize, repetition: usize) {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let mut pw = PartialWitness::new();
    for _ in 0..(1 << nv) {
        let a = builder.add_virtual_target();
        let b = builder.add_virtual_target();
        pw.set_target(a, F::rand());
        pw.set_target(b, F::rand());
        builder.mul(a, b);
    }
    let data = builder.build::<C>();
    let start = Instant::now();
    for _ in 0..repetition {
        let _ = data.prove(pw.clone()).unwrap();
    }
    println!(
        "proving for 2^{} gates: {} us",
        nv,
        start.elapsed().as_micros() / repetition as u128
    );
    let proof = data.prove(pw).unwrap();

    data.verify(proof).unwrap();
}
