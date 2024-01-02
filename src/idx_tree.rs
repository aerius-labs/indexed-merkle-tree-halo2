use halo2_base::{
    gates::{
        circuit::builder::BaseCircuitBuilder, GateChip, GateInstructions, RangeChip,
        RangeInstructions,
    },
    halo2_proofs::plonk::Error,
    poseidon::hasher::{spec::OptimizedPoseidonSpec, PoseidonHasher},
    utils::{BigPrimeField, ScalarField},
    AssignedValue, Context,
};
#[derive(Clone, Debug)]

pub struct IdxLeaf<F: BigPrimeField> {
    val: AssignedValue<F>,
    next_val: AssignedValue<F>,
    next_idx: AssignedValue<F>,
}

#[derive(Clone, Debug)]
pub struct MerCirInput<'a, F: BigPrimeField> {
    range: &'a RangeChip<F>,
    root: &'a AssignedValue<F>,
    leaf: &'a AssignedValue<F>,
    proof: &'a [AssignedValue<F>],
    helper: &'a [AssignedValue<F>],
}
#[derive(Clone, Debug)]
pub struct NonInclusionInp<'a, F: BigPrimeField> {
    range: &'a RangeChip<F>,
    root: AssignedValue<F>,
    lowleaf: IdxLeaf<F>,
    lowleafsib: Vec<AssignedValue<F>>,
    lowleafidx: Vec<AssignedValue<F>>,
    newleafvalue: AssignedValue<F>,
    islargest: bool,
}
pub fn verify_non_inclusion<'a, F: BigPrimeField, const T: usize, const RATE: usize>(
    builder: &mut BaseCircuitBuilder<F>,
    input: NonInclusionInp<F>,
) {
    let ctx = builder.main(0);
    if input.islargest {
        assert!(input.lowleaf.next_val.value().clone() == F::ZERO)
    } else {
        assert!(input.lowleaf.next_val.value() > input.newleafvalue.value());
    }
    let spec = OptimizedPoseidonSpec::<F, T, RATE>::new::<8, 56, 0>();
    let mut hasher = PoseidonHasher::<F, T, RATE>::new(spec);
    hasher.initialize_consts(ctx, input.range.gate());
    let three = ctx.load_constant(F::from(3u64));

    let inp = [
        input.lowleaf.val,
        input.lowleaf.next_val,
        input.lowleaf.next_idx,
    ];

    let lowleaf_hash = hasher.hash_var_len_array(ctx, input.range, &inp, three);

    let ver_input = MerCirInput {
        range: input.range,
        root: &input.root,
        leaf: &lowleaf_hash,
        proof: &input.lowleafsib,
        helper: &input.lowleafidx.to_vec(),
    };
    let mut new: Vec<AssignedValue<F>> = vec![];

    assert_eq!(
        *verify_merkle_proof::<F, T, RATE>(builder, ver_input, &mut new)
            .unwrap()
            .value(),
        F::ONE
    );
    assert_eq!(input.newleafvalue.value() > input.lowleaf.val.value(), true);
}

fn dual_mux<F: ScalarField>(
    ctx: &mut Context<F>,
    gate: &GateChip<F>,
    a: &AssignedValue<F>,
    b: &AssignedValue<F>,
    switch: &AssignedValue<F>,
) -> [AssignedValue<F>; 2] {
    gate.assert_bit(ctx, *switch);

    let a_sub_b = gate.sub(ctx, *a, *b);
    let b_sub_a = gate.sub(ctx, *b, *a);

    let left = gate.mul_add(ctx, b_sub_a, *switch, *a); // left = (b-a)*s + a;
    let right = gate.mul_add(ctx, a_sub_b, *switch, *b); // right = (a-b)*s + b;
    [left, right]
}
pub fn verify_merkle_proof<'a, F: BigPrimeField, const T: usize, const RATE: usize>(
    builder: &mut BaseCircuitBuilder<F>,
    input: MerCirInput<'a, F>,
    make_public: &mut Vec<AssignedValue<F>>,
) -> Result<AssignedValue<F>, Error> {
    let ctx = builder.main(0);
    let gate = input.range.gate();
    let spec = OptimizedPoseidonSpec::<F, T, RATE>::new::<8, 56, 0>();
    let mut hasher = PoseidonHasher::<F, T, RATE>::new(spec);
    hasher.initialize_consts(ctx, gate);
    let two = ctx.load_constant(F::from(2u64));
    let mut computed_hash = ctx.load_witness(input.leaf.value().clone());
    make_public.push(computed_hash.clone());

    for (_, (proof_element, helper)) in input.proof.iter().zip(input.helper.iter()).enumerate() {
        let inp = dual_mux(ctx, gate, &computed_hash, proof_element, helper);
        computed_hash = hasher.hash_var_len_array(ctx, input.range, &inp, two);
    }
    make_public.push(computed_hash.clone());
    Ok(gate.is_equal(ctx, computed_hash, *input.root))
}

fn computemerkleroot<'a, F: BigPrimeField, const T: usize, const RATE: usize>(
    builder: &mut BaseCircuitBuilder<F>,
    leaf: AssignedValue<F>,
    siblings: Vec<AssignedValue<F>>,
    sib_idx: Vec<AssignedValue<F>>,
    range: &'a RangeChip<F>,
) {
    let mut hash = leaf;
    let ctx = builder.main(0);
    let gate = range.gate();

    let spec = OptimizedPoseidonSpec::<F, T, RATE>::new::<8, 56, 0>();
    let hasher = PoseidonHasher::<F, T, RATE>::new(spec);
    let two = ctx.load_constant(F::from(2u64));
    for i in 0..siblings.len() {
        let inp = dual_mux(ctx, gate, &hash, &siblings[i], &sib_idx[i]);
        hash = hasher.hash_var_len_array(ctx, range, &inp, two);
    }
}

#[cfg(test)]
mod test {
    #[test]
    fn test_merkle_verify() {}
}
