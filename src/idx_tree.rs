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
#[derive(Clone, Debug)]
pub struct InsertLeafInp<'a, F: BigPrimeField> {
    range: &'a RangeChip<F>,
    old_root: AssignedValue<F>,
    low_leaf: IdxLeaf<F>,
    low_leaf_proof: Vec<AssignedValue<F>>,
    low_leaf_proof_helper: Vec<AssignedValue<F>>,
    new_root: AssignedValue<F>,
    new_leaf: IdxLeaf<F>,
    new_leaf_index: AssignedValue<F>,
    new_leaf_proof: Vec<AssignedValue<F>>,
    new_leaf_proof_helper: Vec<AssignedValue<F>>,
    is_new_leaf_largest: bool,
}
pub fn verify_non_inclusion<F: BigPrimeField, const T: usize, const RATE: usize>(
    builder: &mut BaseCircuitBuilder<F>,
    input: NonInclusionInp<F>,
) {
    let ctx = builder.main(0);
    if input.islargest {
        assert!(*input.lowleaf.next_val.value() == F::ZERO)
    } else {
        assert!(input.lowleaf.next_val.value() > input.newleafvalue.value());
    }

    let spec = OptimizedPoseidonSpec::<F, T, RATE>::new::<8, 57, 0>();
    let mut hasher = PoseidonHasher::<F, T, RATE>::new(spec);
    hasher.initialize_consts(ctx, input.range.gate());

    let inp = [
        input.lowleaf.val,
        input.lowleaf.next_val,
        input.lowleaf.next_idx,
    ];
    let mut hasher = PoseidonHasher::<F, T, RATE>::new(OptimizedPoseidonSpec::new::<8, 57, 0>());
    let gate = input.range.gate();
    hasher.initialize_consts(ctx, gate);

    let lowleaf_hash = hasher.hash_fix_len_array(ctx, gate, &inp);

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
    //todo
    assert!(input.newleafvalue.value() > input.lowleaf.val.value());
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

    let left = gate.mul_add(ctx, a_sub_b, *switch, *b); // left = (a-b)*s + b;
    let right = gate.mul_add(ctx, b_sub_a, *switch, *a); // right = (b-a)*s + a;

    [left, right]
}
pub fn verify_merkle_proof<F: BigPrimeField, const T: usize, const RATE: usize>(
    builder: &mut BaseCircuitBuilder<F>,
    input: MerCirInput<'_, F>,
    make_public: &mut Vec<AssignedValue<F>>,
) -> Result<AssignedValue<F>, Error> {
    let mut hasher = PoseidonHasher::<F, T, RATE>::new(OptimizedPoseidonSpec::new::<8, 57, 0>());
    let ctx = builder.main(0);
    let gate = input.range.gate();
    hasher.initialize_consts(ctx, gate);

    let mut computed_hash = ctx.load_witness(*input.leaf.value());
    make_public.push(computed_hash);

    for (proof_element, helper) in input.proof.iter().zip(input.helper.iter()) {
        let inp = dual_mux(ctx, gate, &computed_hash, proof_element, helper);
        computed_hash = hasher.hash_fix_len_array(ctx, gate, &inp);
    }
    make_public.push(computed_hash);

    Ok(gate.is_equal(ctx, computed_hash, *input.root))
}

fn computemerkleroot< F: BigPrimeField, const T: usize, const RATE: usize>(
    builder: &mut BaseCircuitBuilder<F>,
    leaf: AssignedValue<F>,
    siblings: Vec<AssignedValue<F>>,
    sib_idx: Vec<AssignedValue<F>>,
    range: & RangeChip<F>,
) -> Result<AssignedValue<F>, Error> {
    let mut hash = leaf;
    let mut hasher = PoseidonHasher::<F, T, RATE>::new(OptimizedPoseidonSpec::new::<8, 57, 0>());
    let ctx = builder.main(0);
    let gate = range.gate();
    hasher.initialize_consts(ctx, gate);

    for i in 0..siblings.len() {
        let inp = dual_mux(ctx, gate, &hash, &siblings[i], &sib_idx[i]);
        hash = hasher.hash_fix_len_array(ctx, gate, &inp);
    }
    Ok(hash)
}

pub fn insert_leaf<F: BigPrimeField, const T: usize, const RATE: usize>(
    builder: &mut BaseCircuitBuilder<F>,
    input: InsertLeafInp<F>,
    make_public: &mut Vec<AssignedValue<F>>,
) {
    let non_inc_inp = NonInclusionInp {
        range: input.range,
        root: input.old_root,
        lowleaf: input.low_leaf.clone(),
        lowleafsib: input.low_leaf_proof.clone(),
        lowleafidx: input.low_leaf_proof_helper.clone(),
        newleafvalue: input.new_leaf.val,
        islargest: input.is_new_leaf_largest,
    };

    verify_non_inclusion::<F, T, RATE>(builder, non_inc_inp);
    let newlowleaf = IdxLeaf {
        val: input.low_leaf.val,
        next_idx: input.new_leaf_index,
        next_val: input.new_leaf.val,
    };

    let mut hasher = PoseidonHasher::<F, T, RATE>::new(OptimizedPoseidonSpec::new::<8, 57, 0>());
    let ctx = builder.main(0);
    let gate = input.range.gate();
    hasher.initialize_consts(ctx, gate);

    //edit

    let inp = [
        newlowleaf.val,
        newlowleaf.next_val,
        newlowleaf.next_idx,
    ];
    let ctx = builder.main(0);

    let leaf_hash = hasher.hash_fix_len_array(ctx, gate, &inp);

    let zero = builder.main(0).load_constant(F::ZERO);

    let intermimroot = computemerkleroot::<F, T, RATE>(
        builder,
        leaf_hash,
        input.low_leaf_proof.clone(),
        input.low_leaf_proof_helper.clone(),
        input.range,
    )
    .unwrap();

    let inp_ver = MerCirInput {
        range: input.range,
        root: &intermimroot,
        leaf: &zero,
        proof: &input.new_leaf_proof.clone(),
        helper: &input.new_leaf_proof_helper.clone(),
    };
    //todo

    verify_proof(zero, 1, intermimroot, input.new_leaf_proof.clone());

    assert_eq!(
        verify_merkle_proof::<F, T, RATE>(builder, inp_ver, make_public)
            .unwrap()
            .value()
            .clone(),
        F::ONE
    );

    assert_eq!(
        input.new_leaf.next_val.value().clone(),
        input.low_leaf.next_val.value().clone()
    );
    assert_eq!(
        input.new_leaf.next_idx.value().clone(),
        input.low_leaf.next_idx.value().clone()
    );

    let inp2 = [
        input.new_leaf.val,
        input.new_leaf.next_val,
        input.new_leaf.next_idx,
    ];

    let newleaf_hash = hasher.hash_fix_len_array(builder.main(0), gate, &inp2);

    assert_eq!(
        computemerkleroot::<F, T, RATE>(
            builder,
            newleaf_hash,
            input.new_leaf_proof.clone(),
            input.new_leaf_proof_helper.clone(),
            input.range
        )
        .unwrap()
        .value()
        .clone(),
        input.new_root.value().clone()
    );
}
pub fn verify_proof<F: BigPrimeField>(
    leaf: AssignedValue<F>,
    index: usize,
    root: AssignedValue<F>,
    proof: Vec<AssignedValue<F>>,
) {
    let mut comp_hash = leaf;
    let mut cur_idx = index as u32;
    let mut builder = BaseCircuitBuilder::<F>::default();
    let gate = GateChip::<F>::default();

    let mut poseidon = PoseidonHasher::<F, 3, 2>::new(OptimizedPoseidonSpec::new::<8, 57, 0>());
    let ctx = builder.main(0);
    poseidon.initialize_consts(ctx, &gate);

    for prf in proof {
        let sib =prf;
        let isleft = cur_idx % 2 == 0;
        comp_hash = if isleft {
            poseidon.hash_fix_len_array(ctx, &gate, &[comp_hash, sib])
        } else {
            poseidon.hash_fix_len_array(ctx, &gate, &[sib, comp_hash])
        };
        cur_idx /= 2;
    }
    assert_eq!(comp_hash.value, root.value);
}

#[cfg(test)]
mod test {
    use ark_std::{end_timer, start_timer};
    use halo2_base::utils::testing::base_test;

    use halo2_base::halo2_proofs::halo2curves::bn256;
    use halo2_base::{
        gates::{
            circuit::{builder::BaseCircuitBuilder, BaseCircuitParams, CircuitBuilderStage},
            GateChip, RangeChip, RangeInstructions,
        },
        halo2_proofs::halo2curves::grumpkin::Fq as Fr,
        halo2_proofs::{circuit::Value, halo2curves::bn256::Bn256},
        poseidon::hasher::{spec::OptimizedPoseidonSpec, PoseidonHasher},
        utils::{fs::gen_srs, BigPrimeField},
        AssignedValue, Context,
    };

    use super::{insert_leaf, IdxLeaf, InsertLeafInp};
    #[warn(dead_code)]
    const T: usize = 3;
    const RATE: usize = 2;
    const R_F: usize = 8;
    const R_P: usize = 57;

    pub fn merkle_help<F: BigPrimeField>(
        leavess: Vec<AssignedValue<F>>,
        ctx: &mut Context<F>,
    ) -> Vec<Vec<AssignedValue<F>>> {
        let mut leaves = leavess.clone();
        let mut help_sib: Vec<Vec<AssignedValue<F>>> = vec![];
        help_sib.push(leaves.clone());

        while leaves.len() > 1 {
            let mut nxtlevel: Vec<AssignedValue<F>> = vec![];
            for (i, _) in leaves.iter().enumerate().step_by(2) {
                let left = leaves[i];
                let right = leaves[i + 1];
                let gate = GateChip::<F>::default();
                let mut poseidon =
                    PoseidonHasher::<F, T, RATE>::new(OptimizedPoseidonSpec::new::<R_F, R_P, 0>());

                poseidon.initialize_consts(ctx, &gate);
                nxtlevel.push(poseidon.hash_fix_len_array(ctx, &gate, &[left, right]));
            }
            help_sib.push(nxtlevel.clone());
            leaves = nxtlevel;
        }

        help_sib
    }
    pub fn get_proof<F: BigPrimeField>(
        index: usize,
        helper: Vec<Vec<AssignedValue<F>>>,
        f_zero: AssignedValue<F>,
        f_one: AssignedValue<F>,
    ) -> (Vec<AssignedValue<F>>, Vec<AssignedValue<F>>) {
        let mut proof: Vec<AssignedValue<F>> = vec![];
        let mut proof_helper: Vec<AssignedValue<F>> = vec![];
        let mut cur_idx = index as u32;

        for i in 0..helper.len() {
            let level = helper[i].clone();
            let isleftleaf = cur_idx % 2 == 0;
            let sibling_idx = if isleftleaf { cur_idx + 1 } else { cur_idx - 1 };
            let sibling = level[sibling_idx as usize];
            proof.push(sibling);
            //todo
            proof_helper.push(if isleftleaf { f_one } else { f_zero });

            cur_idx = cur_idx / 2 as u32;
        }

        (proof, proof_helper)
    }
    pub fn verify_proof(
        leaf: AssignedValue<Fr>,
        index: usize,
        root: AssignedValue<Fr>,
        proof: Vec<AssignedValue<Fr>>,
    ) {
        let mut comp_hash = leaf;
        let mut cur_idx = index as u32;
        let mut builder = BaseCircuitBuilder::<Fr>::default();
        let gate = GateChip::<Fr>::default();

        let mut poseidon =
            PoseidonHasher::<Fr, T, RATE>::new(OptimizedPoseidonSpec::new::<R_F, R_P, 0>());
        let ctx = builder.main(0);
        poseidon.initialize_consts(ctx, &gate);

        for i in 0..proof.len() {
            let sib = proof[i];
            let isleft = cur_idx % 2 == 0;
            comp_hash = if isleft {
                poseidon.hash_fix_len_array(ctx, &gate, &[comp_hash, sib])
            } else {
                poseidon.hash_fix_len_array(ctx, &gate, &[sib, comp_hash])
            };
            cur_idx = cur_idx / 2 as u32;
        }
        assert_eq!(comp_hash.value, root.value);
    }

    #[test]
    fn test_insert_leaf() {
        let treesize = u32::pow(2, 3);
        let mut leaves: Vec<AssignedValue<Fr>> = vec![];

        let mut builder = BaseCircuitBuilder::<Fr>::default();
        let gate = GateChip::<Fr>::default();

        let mut poseidon =
            PoseidonHasher::<Fr, T, RATE>::new(OptimizedPoseidonSpec::new::<R_F, R_P, 0>());
        let ctx = builder.main(0);
        poseidon.initialize_consts(ctx, &gate);

        let f_zero = ctx.load_constant(Fr::zero());
        let f_one = ctx.load_constant(Fr::one());
        for i in 0..treesize {
            if i == 0 {
                leaves.push(poseidon.hash_fix_len_array(ctx, &gate, &[f_zero, f_zero, f_zero]));
            } else {
                leaves.push(f_zero);
            }
        }
        let newVal = ctx.load_constant(Fr::from(69));

        let mut helper = merkle_help::<Fr>(leaves.clone(), ctx);

        let oldroot = helper.pop().unwrap()[0];

        let lowleaf = IdxLeaf {
            val: f_zero,
            next_val: f_zero,
            next_idx: f_zero,
        };

        let (low_leaf_proof, low_leaf_helper) = get_proof(0, helper, f_zero, f_one);
        verify_proof(
            leaves[0].clone(),
            0,
            oldroot.clone(),
            low_leaf_proof.clone(),
        );

        let new_low_leaf = IdxLeaf {
            val: lowleaf.val.clone(),
            next_val: newVal.clone(),
            next_idx: f_one,
        };
        leaves[0] = poseidon.hash_fix_len_array(
            ctx,
            &gate,
            &[
                new_low_leaf.val.clone(),
                new_low_leaf.next_val.clone(),
                new_low_leaf.next_idx.clone(),
            ],
        );

        let mut new_helper = merkle_help::<Fr>(leaves.clone(), ctx);
        let new_helper_root = new_helper.pop().unwrap()[0];

        let (new_leaf_proof, new_leaf_helper) = get_proof(1, new_helper, f_zero, f_one);

        verify_proof(
            leaves[1].clone(),
            1,
            new_helper_root.clone(),
            new_leaf_proof.clone(),
        );

        leaves[1] = poseidon.hash_fix_len_array(ctx, &gate, &[newVal, f_zero, f_zero]);

        let mut new_helper = merkle_help::<Fr>(leaves.clone(), ctx);
        let new_root = new_helper.pop().unwrap()[0];

        verify_proof(
            leaves[1].clone(),
            1,
            new_root.clone(),
            new_leaf_proof.clone(),
        );

        let new_leaf = IdxLeaf {
            val: newVal.clone(),
            next_val: f_zero,
            next_idx: f_zero,
        };

        let new_leaf_idx = f_one;
        let is_new_leaf_largest = true;

        base_test()
            .k(16)
            .lookup_bits(15)
            .expect_satisfied(true)
            .run(|ctx, range| {
                let input = InsertLeafInp::<Fr> {
                    range: range,
                    old_root: oldroot,
                    low_leaf: lowleaf,
                    low_leaf_proof,
                    low_leaf_proof_helper: low_leaf_helper,
                    new_root,
                    new_leaf,
                    new_leaf_index: new_leaf_idx,
                    new_leaf_proof: new_leaf_proof,
                    new_leaf_proof_helper: new_leaf_helper,
                    is_new_leaf_largest,
                };

                let mut make_public: Vec<AssignedValue<Fr>> = vec![];
                let mut builder1 = BaseCircuitBuilder::<Fr>::default();

                println!("TEST STARTS HEAR");
                insert_leaf::<Fr, T, RATE>(&mut builder1, input, &mut make_public);
            });
    }
}
