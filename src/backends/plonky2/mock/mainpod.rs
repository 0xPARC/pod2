//
// MainPod
//

use std::{fmt, iter};

use itertools::zip_eq;
use serde::{Deserialize, Serialize};

use crate::{
    backends::plonky2::{
        basetypes::{Proof, VerifierOnlyCircuitData},
        error::{Error, Result},
        mainpod::{
            extract_merkle_proofs, extract_merkle_transition_proofs, extract_signatures,
            layout_statements, partition_inputs, process_public_statements,
            process_statements_operations, MerkleProofs, MerkleTransitionProofs, Operation,
            OperationAux, SignedBy, Statement,
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
    vd_set: VDSet,
    input_pods: Vec<Box<dyn Pod>>,
    statements_is_pub: Vec<bool>,
    statements: Vec<Statement>,
    /// Universal operations only; imports are verified from `open_input_statements`.
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
        writeln!(f, "MockMainPod ({}):", self.statements_root())?;
        writeln!(f, "  statements:")?;
        let universal_start = 1 + self.params.max_open_input_statement_ops;
        for (i, st) in self.statements.iter().enumerate() {
            let is_pub = self.statements_is_pub[i];
            if i == 0 {
                fmt_statement_index(f, is_pub, st, &"None", i)?;
            } else if i < universal_start {
                if i - 1 < self.open_input_statements.len() {
                    fmt_statement_index(
                        f,
                        is_pub,
                        st,
                        &format_args!("OpenInputStatement open_input_statement_{:02}", i - 1),
                        i,
                    )?;
                } else {
                    fmt_statement_index(f, is_pub, st, &"None", i)?;
                }
            } else {
                fmt_statement_index(f, is_pub, st, &self.operations[i - universal_start], i)?;
            }
        }
        Ok(())
    }
}

fn fmt_statement_index(
    f: &mut fmt::Formatter,
    is_pub: bool,
    st: &Statement,
    op: &dyn fmt::Display,
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
            write!(f, "{:#}", st)?;
        } else {
            write!(f, "{}", st)?;
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
    input_pods: Vec<(usize, Params, VDSet, serde_json::Value)>,
}

impl MockMainPod {
    pub fn new(params: &Params, inputs: MainPodInputs) -> Result<Self> {
        let partitioned = partition_inputs(params, &inputs)?;
        let (statements_is_pub, statements) = layout_statements(params, &inputs, &partitioned)?;

        let local_operations = &partitioned.local_operations;
        let input_statements: Vec<_> = partitioned
            .local_statements
            .iter()
            .map(|(_, st)| st.clone())
            .collect();
        let mut aux_list = vec![OperationAux::None; params.max_statements];
        // Extract Merkle proofs and pad.
        let merkle_proofs =
            extract_merkle_proofs(params, &mut aux_list, local_operations, &input_statements)?;
        // Similarly for Merkle state transition proofs.
        let merkle_transition_proofs =
            extract_merkle_transition_proofs(params, &mut aux_list, local_operations)?;
        let open_input_statements = partitioned.open_input_statements();
        let signatures =
            extract_signatures(params, &mut aux_list, local_operations, &input_statements)?;

        let operations =
            process_statements_operations(params, &statements, &aux_list, &partitioned)?;

        let (pub_sts_mt, _, pub_sts) =
            process_public_statements(params, &inputs, &statements_is_pub, &statements)?;

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
            vd_hash,
            sts_root,
            st_index,
            raw_statement,
            ..
        } = op;
        let pod = &self.input_pods[*pod_index];
        let vd_hash0 = pod.verifier_data_hash();
        if vd_hash0 != *vd_hash {
            return Err(Error::custom(format!(
                "OpenInputStatement uses a vd_hash different than the input pod one: {} != {}",
                vd_hash, vd_hash0
            )));
        }
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

        let universal_start = 1 + self.params.max_open_input_statement_ops;
        if self.statements.len() != universal_start + self.params.max_statements
            || self.statements_is_pub.len() != self.statements.len()
            || self.operations.len() != self.params.max_statements
            || self.open_input_statements.len() > self.params.max_open_input_statement_ops
        {
            return Err(Error::custom(
                "Invalid mock POD statement, publication flag or operation counts",
            ));
        }

        // The initial None and input rows have no universal operations. Check imports directly
        // against their opening data, and require unused rows to remain None.
        for (i, st) in self.statements[..universal_start].iter().enumerate() {
            let data = i
                .checked_sub(1)
                .and_then(|i| self.open_input_statements.get(i));
            let op = if let Some(data) = data {
                self.precheck_open_input_statement(data)?;
                middleware::Operation::OpenInputStatement(data.clone())
            } else {
                middleware::Operation::None
            };
            if !op.check_and_log(&self.params, &st.clone().try_into()?)? {
                return Err(Error::statement_not_check());
            }
        }

        for (st, op) in zip_eq(&self.statements[universal_start..], &self.operations) {
            let op = op.deref(
                &self.statements,
                &self.signatures,
                &self.merkle_proofs,
                &self.merkle_transition_proofs,
            )?;
            if !op.check_and_log(&self.params, &st.clone().try_into()?)? {
                return Err(Error::statement_not_check());
            }
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
    fn deserialize_data(params: Params, data: serde_json::Value, vd_set: VDSet) -> Result<Self> {
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
            .map(|(pod_type, params, vd_set, data)| deserialize_pod(pod_type, params, vd_set, data))
            .collect::<Result<Vec<_>>>()?;
        Ok(Self {
            params,
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

    fn mock_pod_with_imported_statement() -> MockMainPod {
        let params = Params {
            max_input_pods: 1,
            max_statements: 2,
            max_public_statements: 2,
            max_open_input_statement_ops: 2,
            max_custom_predicates: 0,
            max_custom_predicate_verification_ops: 0,
            max_public_key_ops: 0,
            max_signed_by_ops: 0,
            containers: middleware::ParamsContainers {
                state_ops: middleware::ParamsMerkleProofs {
                    max_small: 1,
                    max_medium: 0,
                },
                transition_ops: middleware::ParamsMerkleProofs {
                    max_small: 0,
                    max_medium: 0,
                },
                ..Default::default()
            },
            ..Default::default()
        };
        let mut source = frontend::MainPodBuilder::new(&params, &MOCK_VD_SET);
        let balances = crate::dict!({"balance" => 42});
        let balance = source
            .pub_op(frontend::Operation::dict_contains(balances, "balance", 42))
            .unwrap();
        let source = source.prove(&MockProver {}).unwrap();

        let mut builder = frontend::MainPodBuilder::new(&params, &MOCK_VD_SET);
        builder.add_pod(source).unwrap();
        builder.open_input_st(true, 0, &balance).unwrap();
        builder
            .pub_op(frontend::Operation::eq(balance, 42))
            .unwrap();
        let pod = builder.prove(&MockProver {}).unwrap();
        *(pod.pod as Box<dyn Any>).downcast::<MockMainPod>().unwrap()
    }

    #[test]
    fn imported_statement_and_local_operation_round_trip() {
        use crate::backends::plonky2::mainpod::OperationArg;

        let pod = mock_pod_with_imported_statement();
        pod.verify().unwrap();
        assert_eq!(pod.operations.len(), 2);
        assert_eq!(pod.operations[0].args()[0], OperationArg::Index(1));
        assert_eq!(
            pod.operations[1].op_type(),
            middleware::OperationType::Native(middleware::NativeOperation::None)
        );
        assert_eq!(pod.open_input_statements.len(), 1);
        assert!(pod.statements[2].is_none());
        assert!(pod.statements[4].is_none());
        let public = pod.pub_raw_statements();
        assert_eq!(public[0], pod.statements[1].clone().try_into().unwrap());
        assert_eq!(public[1], pod.statements[3].clone().try_into().unwrap());

        let display = format!("{pod}");
        assert!(display.contains("OpenInputStatement open_input_statement_00"));
        assert!(display.contains("Native(EqualFromEntries) 01 00"));
        assert_eq!(format!("{pod:#}").matches(" <- ").count(), 5);

        let restored = MockMainPod::deserialize_data(
            pod.params.clone(),
            pod.serialize_data(),
            pod.vd_set.clone(),
        )
        .unwrap();
        assert_eq!(restored, pod);
        restored.verify().unwrap();
    }

    #[test]
    fn deserialized_mock_rejects_mismatched_publication_flags() {
        let pod = mock_pod_with_imported_statement();
        for invalid_len in [pod.statements.len() - 1, pod.statements.len() + 1] {
            let mut data = pod.serialize_data();
            data["statements_is_pub"] = serde_json::json!(vec![false; invalid_len]);
            let restored =
                MockMainPod::deserialize_data(pod.params.clone(), data, pod.vd_set.clone())
                    .unwrap();
            let error = restored
                .verify()
                .expect_err("publication flags must match the table");
            assert!(error.to_string().contains("publication flag"));
        }
    }

    #[test]
    fn imported_statement_verification_rejects_tampering() {
        let pod = mock_pod_with_imported_statement();
        let mut wrong_statement = pod.clone();
        wrong_statement.statements[1] = pod.statements[3].clone();
        assert!(wrong_statement.verify().is_err());

        let mut wrong_source = pod.clone();
        wrong_source.open_input_statements[0].sts_root = EMPTY_HASH;
        assert!(wrong_source.verify().is_err());

        let mut wrong_proof = pod.clone();
        wrong_proof.open_input_statements[0]
            .proof
            .siblings
            .push(EMPTY_HASH);
        assert!(wrong_proof.verify().is_err());

        // Rows without opening data must not become an unchecked source of local arguments.
        for padding_index in [0, 2] {
            let mut nonempty_padding = pod.clone();
            nonempty_padding.statements[padding_index] = pod.statements[1].clone();
            assert!(nonempty_padding.verify().is_err());
        }

        let mut missing_operation = pod;
        missing_operation.operations.clear();
        assert!(missing_operation.verify().is_err());
    }

    pub(crate) fn witness_input_with_imported_statement() -> (
        Params,
        crate::backends::plonky2::circuits::mainpod::MainPodVerifyInput,
    ) {
        use crate::backends::plonky2::circuits::mainpod::{AuxTableInput, MainPodVerifyInput};

        let pod = mock_pod_with_imported_statement();
        let mut public_tree = Array::new(Vec::new());
        let sts_mt_proofs = pod
            .public_statements
            .iter()
            .enumerate()
            .map(|(i, st)| public_tree.insert(i, Value::from(st.hash())).unwrap())
            .collect();
        let input = MainPodVerifyInput {
            vds_set: pod.vd_set.clone(),
            vd_mt_proofs: vec![pod.vd_set.get_vds_proof_0()],
            extend_pod0_pub_statements: false,
            statements_is_pub: pod.statements_is_pub.clone(),
            sts_mt_proofs,
            statements: pod.statements.clone(),
            operations: pod.operations.clone(),
            custom_predicates_with_mpt_proofs: Vec::new(),
            pad_open_input_statement: Some(pod.open_input_statements[0].clone()),
            open_input_statements: pod.open_input_statements.clone(),
            aux_table_input: AuxTableInput {
                merkle_proofs: pod.merkle_proofs.clone(),
                merkle_transition_proofs: pod.merkle_transition_proofs.clone(),
                public_key_sks: Vec::new(),
                signed_bys: Vec::new(),
                custom_predicate_verifications: Vec::new(),
            },
        };
        (pod.params, input)
    }

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
