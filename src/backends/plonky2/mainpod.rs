use crate::backends::plonky2::basetypes::C;
use anyhow::{anyhow, Result};
use base64::prelude::*;
use itertools::Itertools;
use log::error;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::witness::PartialWitness;
use plonky2::plonk::config::Hasher;
use plonky2::plonk::proof::ProofWithPublicInputs;
use plonky2::plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig};
use serde::{Deserialize, Serialize};
use std::any::Any;
use std::fmt;

use crate::backends::plonky2::basetypes::{Hash, Value, D, EMPTY_HASH, EMPTY_VALUE, F, VALUE_SIZE};
use crate::backends::plonky2::circuits::mainpod::{
    MainPodVerifyCircuit, MainPodVerifyInput, SignedPodVerifyInput,
};
// TODO: Move the shared components between MockMainPod and MainPod to a common place.
use crate::backends::plonky2::mock::mainpod::{hash_statements, Operation, Statement};
use crate::middleware::{
    self, hash_str, AnchoredKey, MainPodInputs, NativeOperation, NativePredicate, NonePod,
    OperationType, Params, Pod, PodId, PodProver, Predicate, StatementArg, ToFields, KEY_TYPE,
    SELF,
};

pub struct Prover {}

impl PodProver for Prover {
    fn prove(&mut self, params: &Params, inputs: MainPodInputs) -> Result<Box<dyn Pod>> {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let main_pod = MainPodVerifyCircuit {
            params: params.clone(),
        }
        .eval(&mut builder)?;

        let mut pw = PartialWitness::<F>::new();
        let signed_pods_input = inputs
            .signed_pods
            .iter()
            .map(|p| SignedPodVerifyInput {
                // TODO: downcast the pod into `SignedPod`
                kvs: p.kvs().iter().map(|(ak, v)| (ak.1.into(), *v)).collect(),
            })
            .collect();
        let input = MainPodVerifyInput {
            signed_pods: signed_pods_input,
        };
        main_pod.set_targets(&mut pw, &input)?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;

        Ok(Box::new(MainPod {
            params: params.clone(),
            id: todo!(),
            public_statements: todo!(),
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
    fn verify(&self) -> bool {
        // 2. get the id out of the public statements
        let id: PodId = PodId(hash_statements(&self.public_statements, &self.params));
        if id != self.id {
            return false;
        }

        // 1, 3, 4, 5 verification via the zkSNARK proof
        // TODO: cache these artefacts
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let main_pod = MainPodVerifyCircuit {
            params: self.params.clone(),
        }
        .eval(&mut builder)
        .unwrap();

        let data = builder.build::<C>();
        match data.verify(self.proof.clone()) {
            Ok(_) => true,
            Err(e) => {
                error!("MainPod.verify failure: {:?}", e);
                false
            }
        }
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
                            StatementArg::Key(AnchoredKey(pod_id, h)) if *pod_id == SELF => {
                                StatementArg::Key(AnchoredKey(self.id(), *h))
                            }
                            _ => *sa,
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

    fn serialized_proof(&self) -> String {
        todo!()
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::backends::plonky2::mock::signedpod::MockSigner;
    use crate::examples::{zu_kyc_pod_builder, zu_kyc_sign_pod_builders};
    use crate::middleware;

    #[test]
    fn test_main_zu_kyc() -> Result<()> {
        let params = middleware::Params::default();

        let (gov_id_builder, pay_stub_builder, sanction_list_builder) =
            zu_kyc_sign_pod_builders(&params);
        let mut signer = MockSigner {
            pk: "ZooGov".into(),
        };
        let gov_id_pod = gov_id_builder.sign(&mut signer)?;
        let mut signer = MockSigner {
            pk: "ZooDeel".into(),
        };
        let pay_stub_pod = pay_stub_builder.sign(&mut signer)?;
        let mut signer = MockSigner {
            pk: "ZooOFAC".into(),
        };
        let sanction_list_pod = sanction_list_builder.sign(&mut signer)?;
        let kyc_builder =
            zu_kyc_pod_builder(&params, &gov_id_pod, &pay_stub_pod, &sanction_list_pod)?;

        let mut prover = Prover {};
        let kyc_pod = kyc_builder.prove(&mut prover, &params)?;
        let pod = kyc_pod.pod.into_any().downcast::<MainPod>().unwrap();

        assert!(pod.verify()); // TODO
                               // println!("id: {}", pod.id());
                               // println!("pub_statements: {:?}", pod.pub_statements());
        Ok(())
    }
}
