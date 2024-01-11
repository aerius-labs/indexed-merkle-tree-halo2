use halo2_base::{
    Context,
    utils::ScalarField,
    AssignedValue,
    gates::{ GateChip, GateInstructions },
};

// constrains s(a) + (1-s)(b) = output
pub(crate) fn select<F: ScalarField>(
    ctx: &mut Context<F>,
    gate: &GateChip<F>,
    ONE: AssignedValue<F>,
    s: AssignedValue<F>,
    a: AssignedValue<F>,
    b: AssignedValue<F>
) -> AssignedValue<F> {
    gate.assert_bit(ctx, s);
    let a_s = gate.mul(ctx, a, s);
    let one_minus_s = gate.sub(ctx, ONE, s);
    gate.mul_add(ctx, one_minus_s, b, a_s)
}

#[cfg(test)]
mod tests {
    use halo2_base::{
        Context,
        utils::{ ScalarField, testing::base_test },
        gates::GateChip,
        halo2_proofs::halo2curves::grumpkin::Fq as Fr,
    };

    fn select_circuit<F: ScalarField>(ctx: &mut Context<F>, s: bool, a: F, b: F) {
        let gate = GateChip::<F>::default();

        let ONE = ctx.load_constant(F::ONE);
        let s = ctx.load_witness(F::from(s));
        let a = ctx.load_witness(a);
        let b = ctx.load_witness(b);

        let output = super::select(ctx, &gate, ONE, s, a, b);

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
}
