// HACK: Ideally this would live in `benches/`, but `cargo bench` doesn't allow
// custom CLI argument parsing (even with harness disabled). We could also have
// put it in `src/bin/`, but then we wouldn't have access to
// `[dev-dependencies]`.

#[cfg(not(feature = "std"))]
extern crate alloc;

#[cfg(not(feature = "std"))]
use alloc::sync::Arc;

use anyhow::Result;
use log::Level;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CommonCircuitData, VerifierOnlyCircuitData};
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig, PoseidonGoldilocksConfig};
use plonky2::plonk::proof::ProofWithPublicInputs;
use plonky2::plonk::prover::prove;
use plonky2::util::timing::TimingTree;
use plonky2_field::extension::Extendable;

type ProofTuple<F, C, const D: usize> = (
    ProofWithPublicInputs<F, C, D>,
    VerifierOnlyCircuitData<C, D>,
    CommonCircuitData<F, D>,
);

fn start<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>(
    config: &CircuitConfig,
) -> Result<ProofTuple<F, C, D>> {
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

    Ok((proof, data.verifier_only, data.common))
}

fn increment<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>(
    inner: &ProofTuple<F, C, D>,
    config: &CircuitConfig,
) -> Result<ProofTuple<F, C, D>>
where
    C::Hasher: AlgebraicHasher<F>,
{
    let (inner_proof, inner_vd, inner_cd) = inner;
    let mut builder = CircuitBuilder::<F, D>::new(config.clone());
    let pt = builder.add_virtual_proof_with_pis(inner_cd);
    let inner_data = builder.add_virtual_verifier_data(inner_cd.config.fri_config.cap_height);
    builder.verify_proof::<C>(&pt, &inner_data, inner_cd);

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

fn select_max<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>(
    inner1: &ProofTuple<F, C, D>,
    inner2: &ProofTuple<F, C, D>,
    config: &CircuitConfig,
) -> Result<ProofTuple<F, C, D>>
where
    C::Hasher: AlgebraicHasher<F>,
{
    let (inner1_proof, inner1_vd, inner1_cd) = inner1;
    let mut builder = CircuitBuilder::<F, D>::new(config.clone());
    let pt1 = builder.add_virtual_proof_with_pis(inner1_cd);
    let inner1_data = builder.add_virtual_verifier_data(inner1_cd.config.fri_config.cap_height);
    builder.verify_proof::<C>(&pt1, &inner1_data, inner1_cd);

    let (inner2_proof, inner2_vd, inner2_cd) = inner2;
    let pt2 = builder.add_virtual_proof_with_pis(inner2_cd);
    let inner2_data = builder.add_virtual_verifier_data(inner2_cd.config.fri_config.cap_height);
    builder.verify_proof::<C>(&pt2, &inner2_data, inner2_cd);

    let ge = builder.add_virtual_bool_target_safe(); // ge = [inner1 >= inner2]
    {
        // ge: inner1 - inner2 >= 0; !ge: inner2 - inner1 > 0
        let one_sub_two = builder.sub(pt1.public_inputs[0], pt2.public_inputs[0]);
        let two_sub_one = builder.sub(pt2.public_inputs[0], pt1.public_inputs[0]);
        let abs = builder.select(ge, one_sub_two, two_sub_one);
        builder.range_check(abs, 30);
    }
    {
        // res is inner1 * ge + inner2 * (1 - ge)
        let res = builder.select(ge, pt1.public_inputs[0], pt2.public_inputs[0]);
        builder.register_public_input(res);
    }

    let data = builder.build::<C>();

    let mut pw = PartialWitness::new();
    pw.set_proof_with_pis_target(&pt1, inner1_proof);
    pw.set_verifier_data_target(&inner1_data, inner1_vd);
    pw.set_proof_with_pis_target(&pt2, inner2_proof);
    pw.set_verifier_data_target(&inner2_data, inner2_vd);

    pw.set_bool_target(ge, {
        let a = inner1_proof.public_inputs[0].to_canonical_u64();
        let b = inner2_proof.public_inputs[0].to_canonical_u64();
        a >= b
    });

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
    let proof1_1 = start(config)?;
    println!("{:?}", proof1_1.0.public_inputs);
    // Recursively verify the proof
    let proof1_2 = increment::<F, C, D>(&proof1_1, config)?;
    println!("{:?}", proof1_2.0.public_inputs);

    let proof2_1 = start(config)?;
    let proof2_2 = select_max(&proof2_1, &proof1_2, config)?;
    println!("{:?}", proof2_2.0.public_inputs);

    Ok(())
}

fn main() -> Result<()> {
    let config = CircuitConfig::standard_recursion_config();
    benchmark_function(&config)?;

    Ok(())
}
