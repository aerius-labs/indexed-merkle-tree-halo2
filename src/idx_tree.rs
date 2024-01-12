use halo2_base::{
    gates::{ GateChip, GateInstructions, RangeChip, RangeInstructions },
    poseidon::hasher::{ spec::OptimizedPoseidonSpec, PoseidonHasher },
    utils::{ BigPrimeField, ScalarField },
    AssignedValue,
    Context,
};

#[derive(Clone, Debug)]
pub struct IndexedMerkleTreeLeaf<F: BigPrimeField> {
    val: AssignedValue<F>,
    next_val: AssignedValue<F>,
    next_idx: AssignedValue<F>,
}

// constrains s(a) + (1-s)(b) = output
pub(crate) fn select<F: ScalarField>(
    ctx: &mut Context<F>,
    gate: &GateChip<F>,
    one: AssignedValue<F>,
    s: AssignedValue<F>,
    a: AssignedValue<F>,
    b: AssignedValue<F>
) -> AssignedValue<F> {
    gate.assert_bit(ctx, s);
    let a_s = gate.mul(ctx, a, s);
    let one_minus_s = gate.sub(ctx, one, s);
    gate.mul_add(ctx, one_minus_s, b, a_s)
}

pub(crate) fn dual_mux<F: ScalarField>(
    ctx: &mut Context<F>,
    gate: &GateChip<F>,
    a: &AssignedValue<F>,
    b: &AssignedValue<F>,
    switch: &AssignedValue<F>
) -> [AssignedValue<F>; 2] {
    gate.assert_bit(ctx, *switch);

    let a_sub_b = gate.sub(ctx, *a, *b);
    let b_sub_a = gate.sub(ctx, *b, *a);

    let left = gate.mul_add(ctx, a_sub_b, *switch, *b); // left = (a-b)*s + b;
    let right = gate.mul_add(ctx, b_sub_a, *switch, *a); // right = (b-a)*s + a;

    [left, right]
}

fn verify_merkle_proof<F: BigPrimeField, const T: usize, const RATE: usize>(
    ctx: &mut Context<F>,
    range: &RangeChip<F>,
    hasher: &PoseidonHasher<F, T, RATE>,
    root: &AssignedValue<F>,
    leaf: &AssignedValue<F>,
    proof: &[AssignedValue<F>],
    proof_helper: &[AssignedValue<F>]
) {
    let computed_root = compute_merkle_root(ctx, range, hasher, leaf, proof, proof_helper);

    ctx.constrain_equal(&computed_root, root);
}

fn compute_merkle_root<F: BigPrimeField, const T: usize, const RATE: usize>(
    ctx: &mut Context<F>,
    range: &RangeChip<F>,
    hasher: &PoseidonHasher<F, T, RATE>,
    leaf: &AssignedValue<F>,
    proof: &[AssignedValue<F>],
    proof_helper: &[AssignedValue<F>]
) -> AssignedValue<F> {
    let gate = range.gate();

    let mut computed_root = ctx.load_witness(*leaf.value());

    for (proof_element, helper) in proof.iter().zip(proof_helper.iter()) {
        let inp = dual_mux(ctx, gate, &computed_root, proof_element, helper);
        computed_root = hasher.hash_fix_len_array(ctx, gate, &inp);
    }

    computed_root
}

pub fn verify_non_inclusion<F: BigPrimeField, const T: usize, const RATE: usize>(
    ctx: &mut Context<F>,
    range: &RangeChip<F>,
    hasher: &PoseidonHasher<F, T, RATE>,
    root: &AssignedValue<F>,
    low_leaf: &IndexedMerkleTreeLeaf<F>,
    low_leaf_proof: &[AssignedValue<F>],
    low_leaf_proof_helper: &[AssignedValue<F>],
    new_leaf_value: &AssignedValue<F>,
    is_new_leaf_largest: &AssignedValue<F>
) {
    let gate = range.gate();

    let one = ctx.load_constant(F::ONE);
    let zero = ctx.load_zero();

    let is_zero = gate.is_equal(ctx, low_leaf.next_val, zero);
    let is_next_val_greater = range.is_less_than(
        ctx,
        *new_leaf_value,
        low_leaf.next_val,
        range.lookup_bits()
    );
    let is_true = select(ctx, gate, one, *is_new_leaf_largest, is_zero, is_next_val_greater);
    assert_eq!(is_true.value(), &F::ONE);
    ctx.constrain_equal(&is_true, &one);

    let inp = [low_leaf.val, low_leaf.next_val, low_leaf.next_idx];
    let low_leaf_hash = hasher.hash_fix_len_array(ctx, gate, &inp);

    verify_merkle_proof(
        ctx,
        range,
        hasher,
        root,
        &low_leaf_hash,
        low_leaf_proof,
        low_leaf_proof_helper
    );

    range.check_less_than(ctx, low_leaf.val, *new_leaf_value, F::CAPACITY as usize);
}

pub fn insert_leaf<F: BigPrimeField, const T: usize, const RATE: usize>(
    ctx: &mut Context<F>,
    range: &RangeChip<F>,
    old_root: &AssignedValue<F>,
    low_leaf: &IndexedMerkleTreeLeaf<F>,
    low_leaf_proof: &[AssignedValue<F>],
    low_leaf_proof_helper: &[AssignedValue<F>],
    new_root: &AssignedValue<F>,
    new_leaf: &IndexedMerkleTreeLeaf<F>,
    new_leaf_index: &AssignedValue<F>,
    new_leaf_proof: &[AssignedValue<F>],
    new_leaf_proof_helper: &[AssignedValue<F>],
    is_new_leaf_largest: &AssignedValue<F>
) {
    let gate = range.gate();
    let mut hasher = PoseidonHasher::<F, T, RATE>::new(OptimizedPoseidonSpec::new::<8, 57, 0>());
    hasher.initialize_consts(ctx, gate);

    let zero = ctx.load_zero();

    verify_non_inclusion(
        ctx,
        range,
        &hasher,
        old_root,
        low_leaf,
        low_leaf_proof,
        low_leaf_proof_helper,
        &new_leaf.val,
        is_new_leaf_largest
    );

    let newlowleaf = IndexedMerkleTreeLeaf {
        val: low_leaf.val,
        next_idx: *new_leaf_index,
        next_val: new_leaf.val,
    };

    let new_low_leaf_hash = hasher.hash_fix_len_array(
        ctx,
        gate,
        &[newlowleaf.val, newlowleaf.next_val, newlowleaf.next_idx]
    );

    let interim_root = compute_merkle_root(
        ctx,
        range,
        &hasher,
        &new_low_leaf_hash,
        low_leaf_proof,
        low_leaf_proof_helper
    );

    verify_merkle_proof(
        ctx,
        range,
        &hasher,
        &interim_root,
        &zero,
        new_leaf_proof,
        new_leaf_proof_helper
    );

    ctx.constrain_equal(&new_leaf.next_val, &low_leaf.next_val);
    ctx.constrain_equal(&new_leaf.next_idx, &low_leaf.next_idx);

    let new_leaf_hash = hasher.hash_fix_len_array(
        ctx,
        gate,
        &[new_leaf.val, new_leaf.next_val, new_leaf.next_idx]
    );

    let _new_root = compute_merkle_root(
        ctx,
        range,
        &hasher,
        &new_leaf_hash,
        new_leaf_proof,
        new_leaf_proof_helper
    );
    ctx.constrain_equal(new_root, &_new_root);
}

#[cfg(test)]
mod test {
    use halo2_base::utils::testing::base_test;
    use halo2_base::utils::ScalarField;

    use halo2_base::{ gates::GateChip, halo2_proofs::halo2curves::grumpkin::Fq as Fr, Context };

    const T: usize = 3;
    const RATE: usize = 2;
    const R_F: usize = 8;
    const R_P: usize = 57;
    const NUM_BITS: usize = 64;

    fn select_circuit<F: ScalarField>(ctx: &mut Context<F>, s: bool, a: F, b: F) {
        let gate = GateChip::<F>::default();

        let one = ctx.load_constant(F::ONE);
        let s = ctx.load_witness(F::from(s));
        let a = ctx.load_witness(a);
        let b = ctx.load_witness(b);

        let output = super::select(ctx, &gate, one, s, a, b);

        assert_eq!(output.value(), b.value());
    }

    #[test]
    fn test_select() {
        let s = false;
        let a = 69u64;
        let b = 420u64;

        base_test()
            .k(9)
            .expect_satisfied(true)
            .run(|ctx, _| {
                select_circuit(ctx, s, Fr::from(a), Fr::from(b));
            })
    }

    #[test]
    fn test_insert_leaf() {}
}
