use std::any::Any;

use anyhow::{anyhow, Result};
use itertools::Itertools;
use plonky2::{
    iop::witness::PartialWitness,
    plonk::{
        circuit_builder::CircuitBuilder, circuit_data::CircuitConfig, proof::ProofWithPublicInputs,
    },
};

use crate::{
    backends::plonky2::{
        basetypes::{C, D},
        circuits::mainpod::{MainPodVerifyCircuit, MainPodVerifyInput},
        mock::mainpod::{hash_statements, MockMainPod, Statement},
        signedpod::SignedPod,
    },
    middleware::{
        self, AnchoredKey, MainPodInputs, Params, Pod, PodId, PodProver, StatementArg, F, SELF,
    },
};
// TODO: Move the shared components between MockMainPod and MainPod to a common place.

pub struct Prover {}

impl PodProver for Prover {
    // TODO: Be consistent on where we apply the padding, here, or in the set_targets?
    fn prove(&mut self, params: &Params, inputs: MainPodInputs) -> Result<Box<dyn Pod>> {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let main_pod = MainPodVerifyCircuit {
            params: params.clone(),
        }
        .eval(&mut builder)?;

        let mut pw = PartialWitness::<F>::new();
        let signed_pods_input: Vec<SignedPod> = inputs
            .signed_pods
            .iter()
            .map(|p| {
                let p = p
                    .as_any()
                    .downcast_ref::<SignedPod>()
                    .expect("type SignedPod");
                p.clone()
            })
            .collect_vec();

        let merkle_proofs = MockMainPod::extract_merkle_proofs(params, inputs.operations)?;

        // TODO: Move these methods from the mock main pod to a common place
        let statements = MockMainPod::layout_statements(params, &inputs);
        let operations = MockMainPod::process_private_statements_operations(
            params,
            &statements,
            &merkle_proofs,
            inputs.operations,
        )?;
        let operations =
            MockMainPod::process_public_statements_operations(params, &statements, operations)?;

        let public_statements =
            statements[statements.len() - params.max_public_statements..].to_vec();
        // get the id out of the public statements
        let id: PodId = PodId(hash_statements(&public_statements, params));

        let input = MainPodVerifyInput {
            signed_pods: signed_pods_input,
            statements: statements[statements.len() - params.max_statements..].to_vec(),
            operations,
            merkle_proofs,
        };
        main_pod.set_targets(&mut pw, &input)?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;

        Ok(Box::new(MainPod {
            params: params.clone(),
            id,
            public_statements,
            proof,
        }))
    }
}

#[derive(Clone, Debug)]
pub struct MainPod {
    params: Params,
    id: PodId,
    public_statements: Vec<Statement>,
    proof: ProofWithPublicInputs<F, C, 2>,
}

impl Pod for MainPod {
    fn verify(&self) -> Result<()> {
        // 2. get the id out of the public statements
        let id: PodId = PodId(hash_statements(&self.public_statements, &self.params));
        if id != self.id {
            return Err(anyhow!(
                "id does not match, expected {}, computed {}",
                self.id,
                id
            ));
        }

        // 1, 3, 4, 5 verification via the zkSNARK proof
        // TODO: cache these artefacts
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let _main_pod = MainPodVerifyCircuit {
            params: self.params.clone(),
        }
        .eval(&mut builder)?;

        let data = builder.build::<C>();
        data.verify(self.proof.clone())
            .map_err(|e| anyhow!("MainPod proof verification failure: {:?}", e))
    }

    fn id(&self) -> PodId {
        self.id
    }

    fn pub_statements(&self) -> Vec<middleware::Statement> {
        // return the public statements, where when origin=SELF is replaced by origin=self.id()
        self.public_statements
            .iter()
            .cloned()
            .map(|statement| {
                Statement(
                    statement.0.clone(),
                    statement
                        .1
                        .iter()
                        .map(|sa| match &sa {
                            StatementArg::Key(AnchoredKey { pod_id, key }) if *pod_id == SELF => {
                                StatementArg::Key(AnchoredKey::new(self.id(), key.clone()))
                            }
                            _ => sa.clone(),
                        })
                        .collect(),
                )
                .try_into()
                .unwrap()
            })
            .collect()
    }

    fn into_any(self: Box<Self>) -> Box<dyn Any> {
        self
    }
    fn as_any(&self) -> &dyn Any {
        self
    }

    fn serialized_proof(&self) -> String {
        todo!()
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::{
        backends::plonky2::{
            mock::mainpod::MockProver, primitives::signature::SecretKey, signedpod::Signer,
        },
        examples::{zu_kyc_pod_builder, zu_kyc_sign_pod_builders},
        frontend, middleware,
        middleware::RawValue,
        op,
    };

    #[test]
    fn test_main_zu_kyc() -> Result<()> {
        let params = middleware::Params {
            // Currently the circuit uses random access that only supports vectors of length 64.
            // With max_input_main_pods=3 we need random access to a vector of length 73.
            max_input_main_pods: 1,
            ..Default::default()
        };

        let (gov_id_builder, pay_stub_builder, sanction_list_builder) =
            zu_kyc_sign_pod_builders(&params);
        let mut signer = Signer(SecretKey(RawValue::from(1)));
        let gov_id_pod = gov_id_builder.sign(&mut signer)?;
        let mut signer = Signer(SecretKey(RawValue::from(2)));
        let pay_stub_pod = pay_stub_builder.sign(&mut signer)?;
        let mut signer = Signer(SecretKey(RawValue::from(3)));
        let sanction_list_pod = sanction_list_builder.sign(&mut signer)?;
        let kyc_builder =
            zu_kyc_pod_builder(&params, &gov_id_pod, &pay_stub_pod, &sanction_list_pod)?;

        let mut prover = Prover {};
        let kyc_pod = kyc_builder.prove(&mut prover, &params)?;
        let pod = kyc_pod.pod.into_any().downcast::<MainPod>().unwrap();

        pod.verify()
    }

    #[test]
    fn test_mini_0() {
        let params = middleware::Params {
            max_input_signed_pods: 1,
            max_input_main_pods: 1,
            max_signed_pod_values: 6,
            max_statements: 8,
            max_public_statements: 4,
            ..Default::default()
        };

        let mut gov_id_builder = frontend::SignedPodBuilder::new(&params);
        gov_id_builder.insert("idNumber", "4242424242");
        gov_id_builder.insert("dateOfBirth", 1169909384);
        gov_id_builder.insert("socialSecurityNumber", "G2121210");
        let mut signer = Signer(SecretKey(RawValue::from(42)));
        let gov_id = gov_id_builder.sign(&mut signer).unwrap();
        let now_minus_18y: i64 = 1169909388;
        let mut kyc_builder = frontend::MainPodBuilder::new(&params);
        kyc_builder.add_signed_pod(&gov_id);
        kyc_builder
            .pub_op(op!(lt, (&gov_id, "dateOfBirth"), now_minus_18y))
            .unwrap();

        println!("{}", kyc_builder);
        println!();

        // Mock
        let mut prover = MockProver {};
        let kyc_pod = kyc_builder.prove(&mut prover, &params).unwrap();
        let pod = kyc_pod.pod.into_any().downcast::<MockMainPod>().unwrap();
        pod.verify().unwrap();
        println!("{:#}", pod);

        // Real
        let mut prover = Prover {};
        let kyc_pod = kyc_builder.prove(&mut prover, &params).unwrap();
        let pod = kyc_pod.pod.into_any().downcast::<MainPod>().unwrap();
        pod.verify().unwrap()
    }
}
