#![allow(clippy::needless_range_loop)]

use std::{fmt::Debug, marker::PhantomData};

use plonky2::{
    field::extension::{Extendable, FieldExtension},
    gates::gate::Gate,
    hash::hash_types::RichField,
    iop::{
        ext_target::ExtensionTarget,
        generator::{SimpleGenerator, WitnessGeneratorRef},
        target::Target,
        witness::{Witness, WitnessWrite},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CommonCircuitData},
        vars::EvaluationVars,
    },
    util::serialization::{Buffer, IoResult, Read, Write},
};

pub trait SimpleGate: 'static + Send + Sync + Sized + Clone + Debug {
    type F: RichField + Extendable<1>;
    const INPUTS_PER_OP: usize;
    const OUTPUTS_PER_OP: usize;
    const WIRES_PER_OP: usize = Self::INPUTS_PER_OP + Self::OUTPUTS_PER_OP;
    const DEGREE: usize;
    const ID: &'static str;
    fn eval<const D: usize>(
        wires: &[<Self::F as Extendable<D>>::Extension],
    ) -> Vec<<Self::F as Extendable<D>>::Extension>
    where
        Self::F: Extendable<D>;
    fn apply<const D: usize>(
        builder: &mut CircuitBuilder<Self::F, D>,
        targets: &[Target],
    ) -> Vec<Target>
    where
        Self::F: Extendable<D>,
    {
        assert!(targets.len() == Self::INPUTS_PER_OP);
        let gate = GateAdapter::<Self>::new_from_config(&builder.config);
        let (row, slot) = builder.find_slot(gate, &[], &[]);
        let input_start = Self::WIRES_PER_OP * slot;
        let output_start = input_start + Self::INPUTS_PER_OP;
        for (i, &t) in targets.iter().enumerate() {
            builder.connect(t, Target::wire(row, input_start + i));
        }
        (0..Self::OUTPUTS_PER_OP)
            .map(|i| Target::wire(row, output_start + i))
            .collect()
    }
}

#[derive(Debug, Clone)]
pub struct GateAdapter<G: SimpleGate> {
    max_ops: usize,
    recursive_max_wires: usize,
    _gate: PhantomData<G>,
}

#[derive(Debug, Clone)]
pub struct RecursiveGateAdapter<const D: usize, G: SimpleGate> {
    max_ops: usize,
    _gate: PhantomData<G>,
}

#[derive(Debug)]
pub struct RecursiveGenerator<const D: usize, G: SimpleGate> {
    row: usize,
    index: usize,
    _gate: PhantomData<G>,
}

impl<G: SimpleGate> GateAdapter<G> {
    const WIRES_PER_OP: usize = G::INPUTS_PER_OP + G::OUTPUTS_PER_OP;

    pub fn new_from_config(config: &CircuitConfig) -> Self {
        Self {
            max_ops: config.num_routed_wires / Self::WIRES_PER_OP,
            recursive_max_wires: config.num_routed_wires,
            _gate: PhantomData,
        }
    }

    pub fn recursive_gate<const D: usize>(&self) -> RecursiveGateAdapter<D, G> {
        RecursiveGateAdapter::<D, G> {
            max_ops: self.recursive_max_wires / (D * G::WIRES_PER_OP),
            _gate: PhantomData,
        }
    }
}

impl<const D: usize, G: SimpleGate> RecursiveGateAdapter<D, G> {
    const INPUTS_PER_OP: usize = D * G::INPUTS_PER_OP;
    const OUTPUTS_PER_OP: usize = D * G::OUTPUTS_PER_OP;
    const WIRES_PER_OP: usize = Self::INPUTS_PER_OP + Self::OUTPUTS_PER_OP;

    fn apply(
        &self,
        builder: &mut CircuitBuilder<G::F, D>,
        vars: &[ExtensionTarget<D>],
    ) -> Vec<ExtensionTarget<D>>
    where
        G::F: Extendable<D>,
    {
        let (row, slot) = builder.find_slot(self.clone(), &[], &[]);
        for j in 0..G::INPUTS_PER_OP {
            for (k, &v) in vars[j].0.iter().enumerate() {
                builder.connect(
                    v,
                    Target::wire(
                        row,
                        slot * RecursiveGateAdapter::<D, G>::WIRES_PER_OP + j * D + k,
                    ),
                );
            }
        }
        (0..G::OUTPUTS_PER_OP)
            .map(|j| {
                ExtensionTarget(core::array::from_fn(|k| {
                    Target::wire(
                        row,
                        slot * RecursiveGateAdapter::<D, G>::WIRES_PER_OP
                            + RecursiveGateAdapter::<D, G>::INPUTS_PER_OP
                            + j * D
                            + k,
                    )
                }))
            })
            .collect()
    }
}

impl<const D: usize, G: SimpleGate> RecursiveGenerator<D, G> {
    const WIRES_PER_OP: usize = RecursiveGateAdapter::<D, G>::WIRES_PER_OP;
    const INPUTS_PER_OP: usize = RecursiveGateAdapter::<D, G>::INPUTS_PER_OP;
}

#[derive(Debug, Clone)]
pub struct TargetList {
    row: usize,
    offset: usize,
}

impl TargetList {
    pub fn get(&self, index: usize) -> Target {
        Target::wire(self.row, self.offset + index)
    }
}

pub trait WriteTargetList: Write {
    fn write_target_list(&mut self, l: &TargetList) -> IoResult<()> {
        self.write_usize(l.row)?;
        self.write_usize(l.offset)
    }
}

impl<W: Write> WriteTargetList for W {}

pub trait ReadTargetList: Read {
    fn read_target_list(&mut self) -> IoResult<TargetList> {
        Ok(TargetList {
            row: self.read_usize()?,
            offset: self.read_usize()?,
        })
    }
}

impl<R: Read> ReadTargetList for R {}

impl<G: SimpleGate, const D: usize> Gate<G::F, D> for GateAdapter<G>
where
    G::F: RichField + Extendable<D> + Extendable<1>,
{
    fn id(&self) -> String {
        G::ID.to_string()
    }

    fn serialize(
        &self,
        dst: &mut Vec<u8>,
        _common_data: &CommonCircuitData<G::F, D>,
    ) -> IoResult<()> {
        dst.write_usize(self.max_ops)?;
        dst.write_usize(self.recursive_max_wires)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<G::F, D>) -> IoResult<Self>
    where
        Self: Sized,
    {
        Ok(Self {
            max_ops: src.read_usize()?,
            recursive_max_wires: src.read_usize()?,
            _gate: PhantomData,
        })
    }

    fn num_wires(&self) -> usize {
        self.max_ops * Self::WIRES_PER_OP
    }

    fn degree(&self) -> usize {
        G::DEGREE
    }

    fn num_ops(&self) -> usize {
        self.max_ops
    }

    fn num_constants(&self) -> usize {
        0
    }

    fn num_constraints(&self) -> usize {
        self.max_ops * G::OUTPUTS_PER_OP
    }

    fn generators(
        &self,
        row: usize,
        _local_constants: &[G::F],
    ) -> Vec<plonky2::iop::generator::WitnessGeneratorRef<G::F, D>> {
        (0..self.max_ops)
            .map(|index| {
                WitnessGeneratorRef::new(
                    RecursiveGenerator::<1, G> {
                        row,
                        index,
                        _gate: PhantomData,
                    }
                    .adapter(),
                )
            })
            .collect()
    }

    fn eval_unfiltered_base_one(
        &self,
        vars_base: plonky2::plonk::vars::EvaluationVarsBase<G::F>,
        mut yield_constr: plonky2::gates::util::StridedConstraintConsumer<G::F>,
    ) {
        for i in 0..self.max_ops {
            let in_start = Self::WIRES_PER_OP * i;
            let out_start = in_start + G::INPUTS_PER_OP;
            let inputs: Vec<_> = (0..G::INPUTS_PER_OP)
                .map(|j| {
                    <G::F as Extendable<1>>::Extension::from_basefield_array([
                        vars_base.local_wires[in_start + j]
                    ])
                })
                .collect();
            let computed = G::eval::<1>(&inputs[..]);
            yield_constr.many(
                computed.iter().enumerate().map(|(j, &x)| {
                    x.to_basefield_array()[0] - vars_base.local_wires[out_start + j]
                }),
            );
        }
    }

    fn eval_unfiltered(
        &self,
        vars: EvaluationVars<G::F, D>,
    ) -> Vec<<G::F as Extendable<D>>::Extension> {
        let mut constraints = Vec::new();
        for i in 0..self.max_ops {
            let in_start = Self::WIRES_PER_OP * i;
            let out_start = in_start + G::INPUTS_PER_OP;
            let computed = G::eval::<D>(&vars.local_wires[in_start..out_start]);
            constraints.extend(
                computed
                    .iter()
                    .enumerate()
                    .map(|(j, &x)| x - vars.local_wires[out_start + j]),
            );
        }
        constraints
    }

    fn eval_unfiltered_circuit(
        &self,
        builder: &mut plonky2::plonk::circuit_builder::CircuitBuilder<G::F, D>,
        vars: plonky2::plonk::vars::EvaluationTargets<D>,
    ) -> Vec<plonky2::iop::ext_target::ExtensionTarget<D>> {
        let mut constraints = Vec::with_capacity(G::OUTPUTS_PER_OP * self.max_ops);
        for i in 0..self.max_ops {
            let input_start = i * G::WIRES_PER_OP;
            let output_start = input_start + G::INPUTS_PER_OP;
            let computed = self
                .recursive_gate()
                .apply(builder, &vars.local_wires[input_start..output_start]);
            for j in 0..G::OUTPUTS_PER_OP {
                constraints
                    .push(builder.sub_extension(computed[j], vars.local_wires[output_start + j]));
            }
        }
        constraints
    }
}

impl<G: SimpleGate, const D: usize> RecursiveGenerator<D, G> {
    fn deps(&self) -> Vec<Target> {
        let offset = self.index * Self::WIRES_PER_OP;
        (0..Self::INPUTS_PER_OP)
            .map(|i| Target::wire(self.row, offset + i))
            .collect()
    }
}

impl<G, const D: usize, const E: usize> SimpleGenerator<G::F, E> for RecursiveGenerator<D, G>
where
    G: SimpleGate,
    G::F: RichField + Extendable<D> + Extendable<E>,
{
    fn serialize(
        &self,
        dst: &mut Vec<u8>,
        _common_data: &CommonCircuitData<G::F, E>,
    ) -> IoResult<()> {
        dst.write_usize(self.row)?;
        dst.write_usize(self.index)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<G::F, E>) -> IoResult<Self>
    where
        Self: Sized,
    {
        Ok(Self {
            row: src.read_usize()?,
            index: src.read_usize()?,
            _gate: PhantomData,
        })
    }

    fn id(&self) -> String {
        format!("Generator<{},{}>", D, G::ID)
    }

    fn dependencies(&self) -> Vec<Target> {
        self.deps()
    }

    fn run_once(
        &self,
        witness: &plonky2::iop::witness::PartitionWitness<G::F>,
        out_buffer: &mut plonky2::iop::generator::GeneratedValues<G::F>,
    ) -> anyhow::Result<()> {
        let deps = self.deps();
        let inputs: Vec<<G::F as Extendable<D>>::Extension> = (0..G::INPUTS_PER_OP)
            .map(|i| {
                <G::F as Extendable<D>>::Extension::from_basefield_array(core::array::from_fn(
                    |j| witness.get_target(deps[i * D + j]),
                ))
            })
            .collect();
        let out: Vec<<G::F as Extendable<D>>::Extension> = G::eval::<D>(&inputs[..]);
        for (i, x) in out.into_iter().enumerate() {
            for (j, y) in x.to_basefield_array().into_iter().enumerate() {
                let offset = self.index * Self::WIRES_PER_OP;
                let target = Target::wire(self.row, offset + Self::INPUTS_PER_OP + D * i + j);
                out_buffer.set_target(target, y)?;
            }
        }
        Ok(())
    }
}

impl<G: SimpleGate, const D: usize, F> Gate<F, D> for RecursiveGateAdapter<D, G>
where
    G: SimpleGate<F = F>,
    F: RichField + Extendable<D>,
{
    fn id(&self) -> String {
        format!("Recursive<{},{}>", D, G::ID)
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_usize(self.max_ops)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self>
    where
        Self: Sized,
    {
        let max_ops = src.read_usize()?;
        Ok(Self {
            max_ops,
            _gate: PhantomData,
        })
    }

    fn num_wires(&self) -> usize {
        self.max_ops * Self::WIRES_PER_OP
    }

    fn degree(&self) -> usize {
        G::DEGREE
    }

    fn num_ops(&self) -> usize {
        self.max_ops
    }

    fn num_constants(&self) -> usize {
        0
    }

    fn num_constraints(&self) -> usize {
        self.max_ops * Self::OUTPUTS_PER_OP
    }

    fn generators(&self, row: usize, _local_constants: &[F]) -> Vec<WitnessGeneratorRef<F, D>> {
        (0..self.max_ops)
            .map(|index| {
                WitnessGeneratorRef::new(
                    RecursiveGenerator::<D, G> {
                        row,
                        index,
                        _gate: PhantomData,
                    }
                    .adapter(),
                )
            })
            .collect()
    }

    fn eval_unfiltered_base_one(
        &self,
        vars_base: plonky2::plonk::vars::EvaluationVarsBase<F>,
        mut yield_constr: plonky2::gates::util::StridedConstraintConsumer<F>,
    ) {
        for i in 0..self.max_ops {
            let input_start = D * G::WIRES_PER_OP * i;
            let output_start = input_start + D * G::INPUTS_PER_OP;
            let input: Vec<_> = (0..G::INPUTS_PER_OP)
                .map(|j| {
                    F::Extension::from_basefield_array(core::array::from_fn(|k| {
                        vars_base.local_wires[input_start + D * j + k]
                    }))
                })
                .collect();
            let output = G::eval(&input);
            for j in 0..G::OUTPUTS_PER_OP {
                yield_constr.many((0..D).map(|k| {
                    output[j].to_basefield_array()[k]
                        - vars_base.local_wires[output_start + D * j + k]
                }));
            }
        }
    }

    fn eval_unfiltered(&self, vars: EvaluationVars<F, D>) -> Vec<F::Extension> {
        // We think of `vars.local_wires` as a list of G::WIRES_PER_OP
        // elements of ExtensionAlgebra<F,D>.
        // We use the fact that ExtensionAlgebra<F,D> is isomorphic to D copies of
        // F::Extension, with the isomorphism given by (a ⊗ b) ->
        // [a.repeated_frobenius(j) * b for j in 0..D].
        let mut constraints = Vec::with_capacity(D * G::OUTPUTS_PER_OP);
        let mut evals: [Vec<F::Extension>; D] = core::array::from_fn(|_| Vec::new());
        let mut inputs = Vec::with_capacity(G::INPUTS_PER_OP);
        let dth_root_inv = F::DTH_ROOT.inverse();
        let d_inv = F::from_canonical_usize(D).inverse();
        let w_inv = F::W.inverse();
        for i in 0..self.max_ops {
            let input_start = D * G::WIRES_PER_OP * i;
            let output_start = input_start + D * G::INPUTS_PER_OP;
            // Phase factor for Frobenius automorphism
            // application, cf. definition of `repeated_frobenius`
            // in plonky2/field/src/extension/mod.rs.
            let mut phase = F::ONE;
            for ev in evals.iter_mut() {
                inputs.clear();
                // Collect input wires.
                for j in 0..G::INPUTS_PER_OP {
                    let var_start = input_start + D * j;
                    let var: [[F; D]; D] = core::array::from_fn(|k| {
                        vars.local_wires[var_start + k].to_basefield_array()
                    });
                    let mut input = [F::ZERO; D];
                    let mut factor = F::ONE;
                    for k in 0..D {
                        for l in 0..D {
                            let prod = factor * var[k][l];
                            if k + l < D {
                                input[k + l] += prod;
                            } else {
                                input[k + l - D] += F::W * prod;
                            }
                        }
                        factor *= phase;
                    }
                    inputs.push(F::Extension::from_basefield_array(input));
                }
                // Evaluate SimpleGate.
                *ev = G::eval(&inputs);
                phase *= F::DTH_ROOT;
            }
            for j in 0..G::OUTPUTS_PER_OP {
                let mut phase = F::ONE;
                for k in 0..D {
                    let mut output = [F::ZERO; D];
                    let ev: [[F; D]; D] =
                        core::array::from_fn(|l| evals[l][j].to_basefield_array());
                    let mut factor = d_inv;
                    for l in 0..D {
                        for m in 0..D {
                            let prod = factor * ev[l][m];
                            if m >= k {
                                output[m - k] += prod;
                            } else {
                                output[(m + D) - k] += prod * w_inv;
                            }
                        }
                        factor *= phase;
                    }
                    phase *= dth_root_inv;
                    let expected = F::Extension::from_basefield_array(output);
                    let actual = vars.local_wires[output_start + j * D + k];
                    constraints.push(expected - actual);
                }
            }
        }
        constraints
    }

    // Recursive constraint analogue to `eval_unfiltered`.
    fn eval_unfiltered_circuit(
        &self,
        builder: &mut plonky2::plonk::circuit_builder::CircuitBuilder<F, D>,
        vars: plonky2::plonk::vars::EvaluationTargets<D>,
    ) -> Vec<ExtensionTarget<D>> {
        let mut constraints = Vec::with_capacity(D * G::OUTPUTS_PER_OP);
        let mut evals: [Vec<ExtensionTarget<D>>; D] = core::array::from_fn(|_| Vec::new());
        let mut inputs = Vec::with_capacity(G::INPUTS_PER_OP);
        let dth_root_inv = F::DTH_ROOT.inverse();
        let d_inv = F::from_canonical_usize(D).inverse();
        let w_inv_t = builder.constant(F::W.inverse());
        let w_t = builder.constant(F::W);
        for i in 0..self.max_ops {
            let input_start = D * G::WIRES_PER_OP * i;
            let output_start = input_start + D * G::INPUTS_PER_OP;
            let mut phase = F::ONE;
            for ev in evals.iter_mut() {
                inputs.clear();
                for j in 0..G::INPUTS_PER_OP {
                    let var_start = input_start + D * j;
                    let var: [[Target; D]; D] =
                        core::array::from_fn(|k| vars.local_wires[var_start + k].0);
                    let mut input = [builder.zero(); D];
                    let mut factor = F::ONE;
                    for k in 0..D {
                        for l in 0..D {
                            let factor_t = builder.constant(factor);
                            let prod = builder.mul(factor_t, var[k][l]);
                            if k + l < D {
                                input[k + l] = builder.add(input[k + l], prod);
                            } else {
                                let prod_w = builder.mul(w_t, prod);
                                input[k + l - D] = builder.add(input[k + l - D], prod_w);
                            }
                        }
                        factor *= phase;
                    }
                    inputs.push(ExtensionTarget(input));
                }
                *ev = self.apply(builder, &inputs);
                phase *= F::DTH_ROOT;
            }
            for j in 0..G::OUTPUTS_PER_OP {
                let mut phase = F::ONE;
                for k in 0..D {
                    let mut output = [builder.zero(); D];
                    let ev: [[Target; D]; D] = core::array::from_fn(|l| evals[l][j].0);
                    let mut factor = d_inv;
                    for l in 0..D {
                        for m in 0..D {
                            let factor_t = builder.constant(factor);
                            let prod = builder.mul(factor_t, ev[l][m]);
                            if m >= k {
                                output[m - k] = builder.add(output[m - k], prod);
                            } else {
                                let prod_wi = builder.mul(w_inv_t, prod);
                                output[(m + D) - k] = builder.add(output[(m + D) - k], prod_wi);
                            }
                        }
                        factor *= phase;
                    }
                    phase *= dth_root_inv;
                    let expected = ExtensionTarget(output);
                    let actual = vars.local_wires[output_start + j * D + k];
                    constraints.push(builder.sub_extension(expected, actual));
                }
            }
        }
        constraints
    }
}
