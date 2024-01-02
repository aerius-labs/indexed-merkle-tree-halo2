use halo2_base::{
    gates::circuit::{ CircuitBuilderStage, BaseCircuitParams, builder::BaseCircuitBuilder },
    halo2_proofs::{
        poly::kzg::{
            commitment::KZGCommitmentScheme,
            multiopen::VerifierSHPLONK,
            strategy::SingleStrategy,
        },
        halo2curves::{ bn256::Bn256, grumpkin::Fq as Fr },
        plonk::verify_proof,
    },
    AssignedValue,
    utils::fs::gen_srs,
};
use serde::de::DeserializeOwned;
use snark_verifier_sdk::{
    gen_pk,
    halo2::{ gen_snark_shplonk, PoseidonTranscript },
    NativeLoader,
    Snark,
};

pub fn run<T: DeserializeOwned>(
    k: u32,
    circuit_params: BaseCircuitParams,
    f: impl FnOnce(&mut BaseCircuitBuilder<Fr>, T, &mut Vec<AssignedValue<Fr>>),
    inputs: T
) -> Result<Snark, ()> {
    // Generate params for the circuit
    let params = gen_srs(k);

    // Generate a circuit
    let circuit = create_circuit(circuit_params, f, inputs, CircuitBuilderStage::Keygen);

    // Generate Proving Key
    let pk = gen_pk(&params, &circuit, None);
    let vk = pk.get_vk().to_owned();

    // Generate Proof
    let proof = gen_snark_shplonk(&params, &pk, circuit, None::<&str>);

    // Verify Proof
    let strategy = SingleStrategy::new(&params);
    let instance = &proof.instances[0][..];
    let mut transcript = PoseidonTranscript::<NativeLoader, &[u8]>::new::<0>(&proof.proof[..]);
    verify_proof::<
        KZGCommitmentScheme<Bn256>,
        VerifierSHPLONK<'_, Bn256>,
        _,
        _,
        SingleStrategy<'_, Bn256>
    >(&params, &vk, strategy, &[&[instance]], &mut transcript).unwrap();

    Ok(proof)
}

fn create_circuit<T: DeserializeOwned>(
    circuit_params: BaseCircuitParams,
    f: impl FnOnce(&mut BaseCircuitBuilder<Fr>, T, &mut Vec<AssignedValue<Fr>>),
    inputs: T,
    stage: CircuitBuilderStage
) -> BaseCircuitBuilder<Fr> {
    let mut builder = BaseCircuitBuilder::new(false).use_params(circuit_params);

    // builder.main(phase) gets a default "main" thread for the given phase. For most purposes we only need to think about phase 0
    // we need a 64-bit number as input in this case
    // while `some_algorithm_in_zk` was written generically for any field `F`, in practice we use the scalar field of the BN254 curve because that's what the proving system backend uses
    let mut assigned_instances = vec![];
    f(&mut builder, inputs, &mut assigned_instances);
    if !assigned_instances.is_empty() {
        assert_eq!(builder.assigned_instances.len(), 1, "num_instance_columns != 1");
        builder.assigned_instances[0] = assigned_instances;
    }

    if !stage.witness_gen_only() {
        // now `builder` contains the execution trace, and we are ready to actually create the circuit
        // minimum rows is the number of rows used for blinding factors. This depends on the circuit itself, but we can guess the number and change it if something breaks (default 9 usually works)
        let minimum_rows = 20;
        builder.calculate_params(Some(minimum_rows));
    }

    builder
}