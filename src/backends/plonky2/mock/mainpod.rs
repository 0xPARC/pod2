//
// MainPod
//

use std::{fmt, iter};

use serde::{Deserialize, Serialize};

use crate::{
    backends::plonky2::{
        basetypes::{Proof, VerifierOnlyCircuitData},
        error::{Error, Result},
        mainpod::{
            calculate_statements_hash, extract_merkle_proofs,
            extract_merkle_tree_state_transition_proofs, extract_signatures, layout_statements,
            process_private_statements_operations, process_public_statements_operations, Operation,
            OperationAux, SignedBy, Statement,
        },
        mock::emptypod::MockEmptyPod,
        primitives::merkletree::{MerkleClaimAndProof, MerkleTreeStateTransitionProof},
        recursion::hash_verifier_data,
    },
    middleware::{
        self, deserialize_pod, Hash, MainPodInputs, MainPodProver, Params, Pod, PodType, VDSet,
        EMPTY_HASH,
    },
};

pub struct MockProver {}

impl MainPodProver for MockProver {
    fn prove(&self, params: &Params, inputs: MainPodInputs) -> Result<Box<dyn Pod>> {
        Ok(Box::new(MockMainPod::new(params, inputs)?))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct MockMainPod {
    params: Params,
    sts_hash: Hash,
    vd_set: VDSet,
    input_pods: Vec<Box<dyn Pod>>,
    // All statements (inherited + newly introduced by this pod)
    statements: Vec<Statement>,
    operations: Vec<Operation>,
    // public subset of the `statements` vector
    public_statements: Vec<Statement>,
    // All Merkle proofs
    merkle_proofs_containers: Vec<MerkleClaimAndProof>,
    // All Merkle tree state transition proofs
    merkle_tree_state_transition_proofs_containers: Vec<MerkleTreeStateTransitionProof>,
    // All verified signatures
    signatures: Vec<SignedBy>,
}

impl Eq for MockMainPod {}

impl fmt::Display for MockMainPod {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "MockMainPod ({}):", self.sts_hash)?;
        let offset_input_pods = self.offset_input_pods();
        let offset_input_statements = self.offset_input_statements();
        let offset_public_statements = self.offset_public_statements();
        for (i, st) in self.statements.iter().enumerate() {
            if self.params.max_input_pods > 0
                && (i >= offset_input_pods)
                && (i < offset_input_statements)
                && (i - offset_input_pods)
                    .is_multiple_of(self.params.max_input_pods_public_statements)
            {
                let index = (i - offset_input_pods) / self.params.max_input_pods_public_statements;
                let pod = &self.input_pods[index];
                let id = pod.statements_hash();
                let pod_type = pod.pod_type();
                writeln!(
                    f,
                    "  from input recursive Pod {} (id={}, type={:?}):",
                    index, id, pod_type
                )?;
            }
            if i == offset_input_statements {
                writeln!(f, "  private statements:")?;
            }
            if i == offset_public_statements {
                writeln!(f, "  public statements:")?;
            }

            let op = (i >= offset_input_statements)
                .then(|| &self.operations[i - offset_input_statements]);
            fmt_statement_index(f, st, op, i)?;
        }
        Ok(())
    }
}

fn fmt_statement_index(
    f: &mut fmt::Formatter,
    st: &Statement,
    op: Option<&Operation>,
    index: usize,
) -> fmt::Result {
    if f.alternate() || !st.is_none() {
        write!(f, "    {:03}. ", index)?;
        if f.alternate() {
            write!(f, "{:#}", &st)?;
        } else {
            write!(f, "{}", &st)?;
        }
        if let Some(op) = op {
            write!(f, " <- ")?;
            if f.alternate() {
                write!(f, "{:#}", op)?;
            } else {
                write!(f, "{}", op)?;
            }
        }
        writeln!(f)?;
    }
    Ok(())
}

#[derive(Serialize, Deserialize)]
struct Data {
    public_statements: Vec<Statement>,
    operations: Vec<Operation>,
    statements: Vec<Statement>,
    merkle_proofs: Vec<MerkleClaimAndProof>,
    merkle_tree_state_transition_proofs: Vec<MerkleTreeStateTransitionProof>,
    signatures: Vec<SignedBy>,
    input_pods: Vec<(usize, Params, Hash, VDSet, serde_json::Value)>,
}

/// Inputs are sorted as:
/// - Pods
/// - private Statements
/// - public Statements
impl MockMainPod {
    fn offset_input_pods(&self) -> usize {
        1
    }
    fn offset_input_statements(&self) -> usize {
        self.offset_input_pods()
            + self.params.max_input_pods * self.params.max_input_pods_public_statements
    }
    fn offset_public_statements(&self) -> usize {
        self.offset_input_statements() + self.params.max_priv_statements()
    }

    pub fn new(params: &Params, inputs: MainPodInputs) -> Result<Self> {
        let (statements, public_statements) = layout_statements(params, true, &inputs)?;
        dbg!(public_statements.len());
        let mut aux_list = vec![OperationAux::None; params.max_priv_statements()];
        // Extract Merkle proofs and pad.
        let merkle_proofs =
            extract_merkle_proofs(params, &mut aux_list, inputs.operations, inputs.statements)?;
        // Similarly for Merkle state transition proofs.
        let merkle_tree_state_transition_proofs =
            extract_merkle_tree_state_transition_proofs(params, &mut aux_list, inputs.operations)?;
        let signatures =
            extract_signatures(params, &mut aux_list, inputs.operations, inputs.statements)?;

        let operations = process_private_statements_operations(
            params,
            &statements,
            &aux_list,
            inputs.operations,
        )?;
        let operations = process_public_statements_operations(params, &statements, operations)?;

        // get the id out of the public statements
        let sts_hash = calculate_statements_hash(&public_statements, params);

        let pad_pod = MockEmptyPod::new_boxed(params, inputs.vd_set.clone());
        let input_pods: Vec<Box<dyn Pod>> = inputs
            .pods
            .iter()
            .map(|p| dyn_clone::clone_box(*p))
            .chain(iter::repeat_with(|| pad_pod.clone()))
            .take(params.max_input_pods)
            .collect();
        Ok(Self {
            params: params.clone(),
            sts_hash,
            vd_set: inputs.vd_set,
            input_pods,
            public_statements,
            statements,
            operations,
            merkle_proofs_containers: merkle_proofs,
            merkle_tree_state_transition_proofs_containers: merkle_tree_state_transition_proofs,
            signatures,
        })
    }

    pub fn params(&self) -> &Params {
        &self.params
    }
}

impl Pod for MockMainPod {
    fn params(&self) -> &Params {
        &self.params
    }
    fn is_mock(&self) -> bool {
        true
    }
    fn is_main(&self) -> bool {
        true
    }

    fn verify(&self) -> Result<()> {
        for pod in &self.input_pods {
            pod.verify()?;
            if pod.vd_set().root() != self.vd_set.root() {
                return Err(Error::custom(format!(
                    "vds_root in input recursive pod doesn't match MockMainPod vds_root: {} != {}",
                    pod.vd_set().root(),
                    self.vd_set.root(),
                )));
            }
            // If the pod is not mock and main (MainPod family) check that its verifier data is in
            // the set
            if !pod.is_mock() && pod.is_main() {
                let verifier_data = pod.verifier_data();
                let verifier_data_hash = hash_verifier_data(&verifier_data);
                if !self.vd_set.contains(verifier_data_hash) {
                    return Err(Error::custom(format!(
                        "vds_root in input recursive MainPod not in the set: {} not in {}",
                        Hash(verifier_data_hash.elements),
                        self.vd_set.root(),
                    )));
                }
            }
            // Introduction pods can only have Introduction or None statements
            if !pod.is_main() {
                for self_st in pod.pub_self_statements() {
                    match self_st {
                        middleware::Statement::None | middleware::Statement::Intro(_, _) => {}
                        _ => {
                            return Err(Error::custom(format!(
                                "Introduction Pod has a non-introduction statement: {}",
                                self_st,
                            )))
                        }
                    }
                }
            }
        }

        let input_statement_offset = self.offset_input_statements();
        // get the input_statements from the self.statements
        let input_statements = &self.statements[input_statement_offset..];

        // 5. verify that all `input_statements` are correctly generated
        // by `self.operations` (where each operation can only access previous statements)
        let statement_check = input_statements
            .iter()
            .enumerate()
            .map(|(i, s)| {
                self.operations[i]
                    .deref(
                        &self.statements[..input_statement_offset + i],
                        &self.signatures,
                        &self.merkle_proofs_containers,
                        &self.merkle_tree_state_transition_proofs_containers,
                    )?
                    .check_and_log(&self.params, &s.clone().try_into()?)
                    .map_err(|e| e.into())
            })
            .collect::<Result<Vec<_>>>()?;
        if !statement_check.iter().all(|b| *b) {
            return Err(Error::statement_not_check());
        }
        Ok(())
    }

    fn statements_hash(&self) -> Hash {
        self.sts_hash
    }
    fn pod_type(&self) -> (usize, &'static str) {
        (PodType::MockMain as usize, "MockMain")
    }
    fn pub_self_statements(&self) -> Vec<middleware::Statement> {
        self.public_statements
            .iter()
            .cloned()
            .map(|st| st.try_into().expect("valid statement"))
            .collect()
    }

    fn verifier_data_hash(&self) -> Hash {
        EMPTY_HASH
    }
    fn verifier_data(&self) -> VerifierOnlyCircuitData {
        panic!("MockMainPod can't be verified in a recursive MainPod circuit");
    }
    fn common_hash(&self) -> String {
        panic!("MockMainPod can't be verified in a recursive MainPod circuit");
    }
    fn proof(&self) -> Proof {
        panic!("MockMainPod can't be verified in a recursive MainPod circuit");
    }
    fn vd_set(&self) -> &VDSet {
        &self.vd_set
    }

    fn serialize_data(&self) -> serde_json::Value {
        let input_pods = self
            .input_pods
            .iter()
            .map(|p| {
                (
                    p.pod_type().0,
                    p.params().clone(),
                    p.statements_hash(),
                    p.vd_set().clone(),
                    p.serialize_data(),
                )
            })
            .collect();
        serde_json::to_value(Data {
            public_statements: self.public_statements.clone(),
            operations: self.operations.clone(),
            statements: self.statements.clone(),
            merkle_proofs: self.merkle_proofs_containers.clone(),
            merkle_tree_state_transition_proofs: self
                .merkle_tree_state_transition_proofs_containers
                .clone(),
            signatures: self.signatures.clone(),
            input_pods,
        })
        .expect("serialization to json")
    }
    // MockMainPods include some internal private state which is necessary
    // for verification. In non-mock Pods, this state will not be necessary,
    // as the public statements can be verified using a ZK proof.
    fn deserialize_data(
        params: Params,
        data: serde_json::Value,
        vd_set: VDSet,
        id: Hash,
    ) -> Result<Self> {
        let Data {
            public_statements,
            operations,
            statements,
            merkle_proofs,
            merkle_tree_state_transition_proofs,
            signatures,
            input_pods,
        } = serde_json::from_value(data)?;
        let input_pods = input_pods
            .into_iter()
            .map(|(pod_type, params, id, vd_set, data)| {
                deserialize_pod(pod_type, params, id, vd_set, data)
            })
            .collect::<Result<Vec<_>>>()?;
        Ok(Self {
            params,
            sts_hash: id,
            vd_set,
            input_pods,
            public_statements,
            operations,
            statements,
            merkle_proofs_containers: merkle_proofs,
            merkle_tree_state_transition_proofs_containers: merkle_tree_state_transition_proofs,
            signatures,
        })
    }
}

#[cfg(test)]
pub mod tests {
    use std::any::Any;

    use super::*;
    use crate::{
        backends::plonky2::{primitives::ec::schnorr::SecretKey, signer::Signer},
        examples::{
            great_boy_pod_full_flow, tickets_pod_full_flow, zu_kyc_pod_builder, zu_kyc_pod_request,
            zu_kyc_sign_dict_builders, MOCK_VD_SET,
        },
        frontend, middleware,
        middleware::{Signer as _, Value},
    };

    #[test]
    fn test_mock_main_zu_kyc() -> frontend::Result<()> {
        let params = middleware::Params::default();
        let vd_set = &*MOCK_VD_SET;
        let (gov_id_builder, pay_stub_builder) = zu_kyc_sign_dict_builders(&params);
        let gov_id_signer = Signer(SecretKey(1u32.into()));
        let gov_id_pod = gov_id_builder.sign(&gov_id_signer)?;
        let pay_stub_signer = Signer(SecretKey(2u32.into()));
        let pay_stub_pod = pay_stub_builder.sign(&pay_stub_signer)?;
        let kyc_builder = zu_kyc_pod_builder(&params, vd_set, &gov_id_pod, &pay_stub_pod)?;

        let prover = MockProver {};
        let kyc_pod = kyc_builder.prove(&prover)?;
        let pod = (kyc_pod.pod as Box<dyn Any>)
            .downcast::<MockMainPod>()
            .unwrap();

        println!("{:#}", pod);

        pod.verify()?;

        let request = zu_kyc_pod_request(
            &Value::from(gov_id_signer.public_key()),
            &Value::from(pay_stub_signer.public_key()),
        )?;
        assert!(request.exact_match_pod(&*pod).is_ok());

        Ok(())
    }

    #[test]
    fn test_mock_main_great_boy() -> frontend::Result<()> {
        let great_boy_builder = great_boy_pod_full_flow()?;

        let prover = MockProver {};
        let great_boy_pod = great_boy_builder.prove(&prover)?;
        let pod = (great_boy_pod.pod as Box<dyn Any>)
            .downcast::<MockMainPod>()
            .unwrap();

        println!("{}", pod);

        pod.verify()?;

        Ok(())
    }

    #[test]
    fn test_mock_main_tickets() -> frontend::Result<()> {
        let params = middleware::Params::default();
        let tickets_builder = tickets_pod_full_flow(&params, &MOCK_VD_SET)?;
        let prover = MockProver {};
        let proof_pod = tickets_builder.prove(&prover)?;
        let pod = (proof_pod.pod as Box<dyn Any>)
            .downcast::<MockMainPod>()
            .unwrap();

        println!("{}", pod);
        pod.verify()?;

        Ok(())
    }
}
