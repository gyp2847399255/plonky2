// HACK: Ideally this would live in `benches/`, but `cargo bench` doesn't allow
// custom CLI argument parsing (even with harness disabled). We could also have
// put it in `src/bin/`, but then we wouldn't have access to
// `[dev-dependencies]`.

#[cfg(not(feature = "std"))]
extern crate alloc;

#[cfg(not(feature = "std"))]
use alloc::sync::Arc;
#[cfg(feature = "std")]
use std::sync::Arc;
use std::time::SystemTime;

use anyhow::{anyhow, Context as _, Result};
use itertools::Itertools;
use log::{info, Level, LevelFilter};
use plonky2::gadgets::lookup::TIP5_TABLE;
use plonky2::gates::noop::NoopGate;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CommonCircuitData, VerifierOnlyCircuitData};
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig, PoseidonGoldilocksConfig};
use plonky2::plonk::proof::{CompressedProofWithPublicInputs, ProofWithPublicInputs};
use plonky2::plonk::prover::prove;
use plonky2::util::timing::TimingTree;
use plonky2_field::extension::Extendable;

type ProofTuple<F, C, const D: usize> = (
    ProofWithPublicInputs<F, C, D>,
    VerifierOnlyCircuitData<C, D>,
    CommonCircuitData<F, D>,
);

fn dummy_proof<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>(
    config: &CircuitConfig,
) -> Result<ProofTuple<F, C, D>> {
    // 'size' is in degree, but we want number of noop gates. A non-zero amount of padding will be added and size will be rounded to the next power of two. To hit our target size, we go just under the previous power of two and hope padding is less than half the proof.

    let mut builder = CircuitBuilder::<F, D>::new(config.clone());
    let initial = builder.constant(F::from_canonical_u32(0));
    let increment = builder.constant(F::from_canonical_u32(1));
    let add_target = builder.add(initial, increment);
    builder.register_public_input(add_target);

    let data = builder.build::<C>();

    let inputs = PartialWitness::new();

    let mut timing = TimingTree::new("prove", Level::Debug);
    let proof = prove::<F, C, D>(&data.prover_only, &data.common, inputs, &mut timing)?;
    timing.print();
    data.verify(proof.clone())?;

    println!(
        "public input: {}, len: {}",
        proof.public_inputs[0],
        proof.public_inputs.len()
    );

    Ok((proof, data.verifier_only, data.common))
}

fn ivc<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    InnerC: GenericConfig<D, F = F>,
    const D: usize,
>(
    inner: &ProofTuple<F, InnerC, D>,
    config: &CircuitConfig,
) -> Result<ProofTuple<F, C, D>>
where
    InnerC::Hasher: AlgebraicHasher<F>,
{
    let (inner_proof, inner_vd, inner_cd) = inner;
    let mut builder = CircuitBuilder::<F, D>::new(config.clone());
    let pt = builder.add_virtual_proof_with_pis(inner_cd);
    let inner_data = builder.add_virtual_verifier_data(inner_cd.config.fri_config.cap_height);
    builder.verify_proof::<InnerC>(&pt, &inner_data, inner_cd);

    let increment = builder.constant(F::from_canonical_u32(1));
    let add_target = builder.add(pt.public_inputs[0], increment);
    builder.register_public_input(add_target);

    let data = builder.build::<C>();

    let mut pw = PartialWitness::new();
    pw.set_proof_with_pis_target(&pt, inner_proof);
    pw.set_verifier_data_target(&inner_data, inner_vd);

    let mut timing = TimingTree::new("prove", Level::Debug);
    let proof = prove::<F, C, D>(&data.prover_only, &data.common, pw, &mut timing)?;
    timing.print();

    data.verify(proof.clone())?;

    Ok((proof, data.verifier_only, data.common))
}

pub fn benchmark_function(config: &CircuitConfig) -> Result<()> {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    // Start with a dummy proof of specified size
    let inner = dummy_proof(config)?;
    println!("{:?}", inner.0.public_inputs);
    // Recursively verify the proof
    let middle = ivc::<F, C, C, D>(&inner, config)?;
    println!("{:?}", middle.0.public_inputs);

    // Add a second layer of recursion to shrink the proof size further
    // let outer = recursive_proof::<F, C, C, D>(&middle, config, None)?;
    // println!("{:?}", outer.0.public_inputs);

    Ok(())
}

fn main() -> Result<()> {
    let config = CircuitConfig::standard_recursion_config();
    benchmark_function(&config)?;

    Ok(())
}
