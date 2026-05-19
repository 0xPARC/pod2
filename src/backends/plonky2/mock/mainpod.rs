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
            extract_merkle_proofs, extract_merkle_transition_proofs, extract_open_input_statements,
            extract_signatures, layout_statements, process_public_statements,
            process_public_statements_operations, process_statements_operations, MerkleProofs,
            MerkleTransitionProofs, Operation, OperationAux, SignedBy, Statement,
        },
        mock::emptypod::MockEmptyPod,
        recursion::hash_verifier_data,
    },
    middleware::{
        self, containers::Array, deserialize_pod, Hash, InputPodOpenStatement, MainPodInputs,
        MainPodProver, Params, Pod, PodType, VDSet, EMPTY_HASH,
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
    pub_sts_root: Hash,
    vd_set: VDSet,
    input_pods: Vec<Box<dyn Pod>>,
    statements_is_pub: Vec<bool>,
    statements: Vec<Statement>,
    operations: Vec<Operation>,
    public_statements: Vec<Statement>,
    public_statements_mt: Array,
    // All Merkle proofs for containers
    merkle_proofs: MerkleProofs,
    // All Merkle tree state transition proofs for containers
    merkle_transition_proofs: MerkleTransitionProofs,
    open_input_statements: Vec<InputPodOpenStatement>,
    // All verified signatures
    signatures: Vec<SignedBy>,
}

impl Eq for MockMainPod {}

impl fmt::Display for MockMainPod {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "MockMainPod ({}):", self.pub_sts_root)?;
        writeln!(f, "  statements:")?;
        for (i, st) in self.statements.iter().enumerate() {
            let is_pub = self.statements_is_pub[i];
            let op = &self.operations[i];
            fmt_statement_index(f, is_pub, st, op, i)?;
        }
        Ok(())
    }
}

fn fmt_statement_index(
    f: &mut fmt::Formatter,
    is_pub: bool,
    st: &Statement,
    op: &Operation,
    index: usize,
) -> fmt::Result {
    if f.alternate() || !st.is_none() {
        write!(f, "    {:03}. ", index)?;
        if is_pub {
            write!(f, "pub ")?;
        } else {
            write!(f, "prv ")?;
        }
        if f.alternate() {
            write!(f, "{:#}", &st)?;
        } else {
            write!(f, "{}", &st)?;
        }
        write!(f, " <- ")?;
        if f.alternate() {
            write!(f, "{:#}", op)?;
        } else {
            write!(f, "{}", op)?;
        }
        writeln!(f)?;
    }
    Ok(())
}

#[derive(Serialize, Deserialize)]
struct Data {
    // TODO: Change to inherited pub statements to reduce data
    public_statements: Vec<Statement>,
    public_statements_mt: Array,
    operations: Vec<Operation>,
    statements_is_pub: Vec<bool>,
    statements: Vec<Statement>,
    merkle_proofs: MerkleProofs,
    merkle_transition_proofs: MerkleTransitionProofs,
    open_input_statements: Vec<InputPodOpenStatement>,
    signatures: Vec<SignedBy>,
    input_pods: Vec<(usize, Params, Hash, VDSet, serde_json::Value)>,
}

impl MockMainPod {
    pub fn new(params: &Params, inputs: MainPodInputs) -> Result<Self> {
        let (statements_is_pub, statements) = layout_statements(params, &inputs)?;

        let input_statements: Vec<_> = inputs.statements.iter().map(|(_, st)| st.clone()).collect();
        let mut aux_list = vec![OperationAux::None; params.max_statements];
        // Extract Merkle proofs and pad.
        let merkle_proofs =
            extract_merkle_proofs(params, &mut aux_list, inputs.operations, &input_statements)?;
        // Similarly for Merkle state transition proofs.
        let merkle_transition_proofs =
            extract_merkle_transition_proofs(params, &mut aux_list, inputs.operations)?;
        let open_input_statements =
            extract_open_input_statements(params, &mut aux_list, inputs.operations)?;
        let signatures =
            extract_signatures(params, &mut aux_list, inputs.operations, &input_statements)?;

        let operations =
            process_statements_operations(params, &statements, &aux_list, inputs.operations)?;
        let operations = process_public_statements_operations(&statements, operations)?;

        let (pub_sts_mt, _, pub_sts) =
            process_public_statements(&inputs, &statements_is_pub, &statements)?;

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
            pub_sts_root: pub_sts_mt.commitment(),
            vd_set: inputs.vd_set,
            input_pods,
            public_statements: pub_sts,
            public_statements_mt: pub_sts_mt,
            statements_is_pub,
            statements,
            operations,
            merkle_proofs,
            merkle_transition_proofs,
            open_input_statements,
            signatures,
        })
    }

    pub fn params(&self) -> &Params {
        &self.params
    }

    fn precheck_open_input_statement(&self, op: &InputPodOpenStatement) -> Result<()> {
        let InputPodOpenStatement {
            pod_index,
            sts_root,
            st_index,
            raw_statement,
            ..
        } = op;
        let pod = &self.input_pods[*pod_index];
        let sts_root0 = pod.statements_root();
        if sts_root0 != *sts_root {
            return Err(Error::custom(format!("OpenInputStatement uses a statements root different than the input pod one: {} != {}", sts_root, sts_root0)));
        }
        let raw_statement0 = &pod.pub_raw_statements()[*st_index];
        if raw_statement0 != raw_statement {
            return Err(Error::custom(format!("OpenInputStatement uses a raw_statement different than the input pod one: {} != {}", raw_statement0, raw_statement)));
        }
        // Introduction pods can only have Introduction or None statements
        if !pod.is_main() {
            match raw_statement0 {
                middleware::Statement::None | middleware::Statement::Intro(_, _) => {}
                _ => {
                    return Err(Error::custom(format!(
                        "Introduction Pod has a non-introduction statement: {}",
                        raw_statement0,
                    )))
                }
            }
        }
        Ok(())
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
                for self_st in pod.pub_raw_statements() {
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

        // 5. verify that all `input_statements` are correctly generated
        // by `self.operations` (where each operation can only access previous statements)
        let statement_check = self
            .statements
            .iter()
            .enumerate()
            .map(|(i, s)| {
                let op = self.operations[i].deref(
                    &self.statements,
                    &self.signatures,
                    &self.merkle_proofs,
                    &self.merkle_transition_proofs,
                    &self.open_input_statements,
                )?;
                if let middleware::Operation::OpenInputStatement(op) = &op {
                    self.precheck_open_input_statement(op)?;
                }
                op.check_and_log(&self.params, &s.clone().try_into()?)
                    .map_err(|e| e.into())
            })
            .collect::<Result<Vec<_>>>()?;
        if !statement_check.iter().all(|b| *b) {
            return Err(Error::statement_not_check());
        }
        Ok(())
    }

    fn pod_type(&self) -> (usize, &'static str) {
        (PodType::MockMain as usize, "MockMain")
    }
    fn pub_raw_statements_mt(&self) -> Array {
        self.public_statements_mt.clone()
    }

    fn pub_raw_statements(&self) -> Vec<middleware::Statement> {
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
                    p.statements_root(),
                    p.vd_set().clone(),
                    p.serialize_data(),
                )
            })
            .collect();
        serde_json::to_value(Data {
            public_statements: self.public_statements.clone(),
            public_statements_mt: self.public_statements_mt.clone(),
            operations: self.operations.clone(),
            statements_is_pub: self.statements_is_pub.clone(),
            statements: self.statements.clone(),
            merkle_proofs: self.merkle_proofs.clone(),
            merkle_transition_proofs: self.merkle_transition_proofs.clone(),
            open_input_statements: self.open_input_statements.clone(),
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
        sts_root: Hash,
    ) -> Result<Self> {
        let Data {
            public_statements,
            public_statements_mt, // TODO: Derive this from public_statements
            operations,
            statements,
            statements_is_pub,
            merkle_proofs,
            merkle_transition_proofs,
            open_input_statements,
            signatures,
            input_pods,
        } = serde_json::from_value(data)?;
        let input_pods = input_pods
            .into_iter()
            .map(|(pod_type, params, sts_root, vd_set, data)| {
                deserialize_pod(pod_type, params, sts_root, vd_set, data)
            })
            .collect::<Result<Vec<_>>>()?;
        Ok(Self {
            params,
            pub_sts_root: sts_root,
            vd_set,
            input_pods,
            public_statements,
            public_statements_mt,
            operations,
            statements_is_pub,
            statements,
            merkle_proofs,
            merkle_transition_proofs,
            open_input_statements,
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
        frontend::{self},
        middleware,
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
