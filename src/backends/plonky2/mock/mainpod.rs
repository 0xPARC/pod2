//
// MainPod
//

use std::{fmt, iter};

use itertools::Itertools;
use serde::{Deserialize, Serialize};

use crate::{
    backends::plonky2::{
        basetypes::{Proof, VerifierOnlyCircuitData},
        error::{Error, Result},
        mainpod::{
            calculate_id, extract_merkle_proofs, layout_statements,
            process_private_statements_operations, process_public_statements_operations, Operation,
            OperationAux, Statement,
        },
        mock::emptypod::MockEmptyPod,
        primitives::merkletree::MerkleClaimAndProof,
        recursion::hash_verifier_data,
        signedpod::SignedPod,
    },
    middleware::{
        self, deserialize_pod, deserialize_signed_pod, hash_str, AnchoredKey, Hash, MainPodInputs,
        NativeOperation, NativePredicate, OperationType, Params, Pod, PodId, PodProver, PodType,
        Predicate, RecursivePod, StatementArg, VDSet, Value, KEY_TYPE, SELF,
    },
};

pub struct MockProver {}

impl PodProver for MockProver {
    fn prove(
        &self,
        params: &Params,
        _vd_set: &VDSet,
        inputs: MainPodInputs,
    ) -> Result<Box<dyn RecursivePod>> {
        Ok(Box::new(MockMainPod::new(params, inputs)?))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct MockMainPod {
    params: Params,
    id: PodId,
    vd_set: VDSet,
    input_signed_pods: Vec<Box<dyn Pod>>,
    input_recursive_pods: Vec<Box<dyn RecursivePod>>,
    // All statements (inherited + newly introduced by this pod)
    statements: Vec<Statement>,
    operations: Vec<Operation>,
    // public subset of the `statements` vector
    public_statements: Vec<Statement>,
    // All Merkle proofs
    merkle_proofs_containers: Vec<MerkleClaimAndProof>,
}

impl Eq for MockMainPod {}

impl fmt::Display for MockMainPod {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "MockMainPod ({}):", self.id)?;
        let offset_input_signed_pods = Self::offset_input_signed_pods();
        let offset_input_recursive_pods = self.offset_input_recursive_pods();
        let offset_input_statements = self.offset_input_statements();
        let offset_public_statements = self.offset_public_statements();
        for (i, st) in self.statements.iter().enumerate() {
            if self.params.max_input_signed_pods > 0
                && (i >= offset_input_signed_pods && i < offset_input_recursive_pods)
                && (i - offset_input_signed_pods).is_multiple_of(self.params.max_signed_pod_values)
            {
                let index = (i - offset_input_signed_pods) / self.params.max_signed_pod_values;
                let pod = &self.input_signed_pods[index];
                let id = pod.id();
                let pod_type = pod.pod_type();
                writeln!(
                    f,
                    "  from input SignedPod {} (id={}, type={:?}):",
                    index, id, pod_type
                )?;
            }
            if self.params.max_input_recursive_pods > 0
                && (i >= offset_input_recursive_pods)
                && (i < offset_input_statements)
                && (i - offset_input_recursive_pods)
                    .is_multiple_of(self.params.max_input_pods_public_statements)
            {
                let index = (i - offset_input_recursive_pods)
                    / self.params.max_input_pods_public_statements;
                let pod = &self.input_recursive_pods[index];
                let id = pod.id();
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
    input_signed_pods: Vec<(usize, PodId, serde_json::Value)>,
    input_recursive_pods: Vec<(usize, Params, PodId, VDSet, serde_json::Value)>,
}

/// Inputs are sorted as:
/// - SignedPods
/// - MainPods
/// - private Statements
/// - public Statements
impl MockMainPod {
    fn offset_input_signed_pods() -> usize {
        1
    }
    fn offset_input_recursive_pods(&self) -> usize {
        Self::offset_input_signed_pods()
            + self.params.max_input_signed_pods * self.params.max_signed_pod_values
    }
    fn offset_input_statements(&self) -> usize {
        self.offset_input_recursive_pods()
            + self.params.max_input_recursive_pods * self.params.max_input_pods_public_statements
    }
    fn offset_public_statements(&self) -> usize {
        self.offset_input_statements() + self.params.max_priv_statements()
    }

    pub fn new(params: &Params, inputs: MainPodInputs) -> Result<Self> {
        let (statements, public_statements) = layout_statements(params, true, &inputs)?;
        let mut aux_list = vec![OperationAux::None; params.max_priv_statements()];
        // Extract Merkle proofs and pad.
        let merkle_proofs =
            extract_merkle_proofs(params, &mut aux_list, inputs.operations, inputs.statements)?;

        let operations = process_private_statements_operations(
            params,
            &statements,
            &aux_list,
            inputs.operations,
        )?;
        let operations = process_public_statements_operations(params, &statements, operations)?;

        // get the id out of the public statements
        let id: PodId = PodId(calculate_id(&public_statements, params));

        let pad_signed_pod: Box<dyn Pod> = Box::new(SignedPod::dummy());
        let input_signed_pods: Vec<Box<dyn Pod>> = inputs
            .signed_pods
            .iter()
            .map(|p| dyn_clone::clone_box(*p))
            .chain(iter::repeat_with(|| pad_signed_pod.clone()))
            .take(params.max_input_signed_pods)
            .collect();
        let pad_pod = MockEmptyPod::new_boxed(params, inputs.vd_set.clone());
        let input_recursive_pods: Vec<Box<dyn RecursivePod>> = inputs
            .recursive_pods
            .iter()
            .map(|p| dyn_clone::clone_box(*p))
            .chain(iter::repeat_with(|| pad_pod.clone()))
            .take(params.max_input_recursive_pods)
            .collect();
        Ok(Self {
            params: params.clone(),
            id,
            vd_set: inputs.vd_set,
            input_signed_pods,
            input_recursive_pods,
            public_statements,
            statements,
            operations,
            merkle_proofs_containers: merkle_proofs,
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

    fn verify(&self) -> Result<()> {
        // 1. Verify input pods
        for pod in &self.input_signed_pods {
            pod.verify()?;
        }
        for pod in &self.input_recursive_pods {
            pod.verify()?;
            if pod.vd_set().root() != self.vd_set.root() {
                return Err(Error::custom(format!(
                    "vds_root in input recursive pod doesn't match MockMainPod vds_root: {} != {}",
                    pod.vd_set().root(),
                    self.vd_set.root(),
                )));
            }
            let (pod_type, _) = pod.pod_type();
            // If the pod is not mock, check that its verifier data is in the set
            if pod_type != PodType::MockMain as usize && pod_type != PodType::MockEmpty as usize {
                let verifier_data = pod.verifier_data();
                let verifier_data_hash = hash_verifier_data(&verifier_data);
                if !self.vd_set.contains(verifier_data_hash) {
                    return Err(Error::custom(format!(
                        "vds_root in input recursive pod not in the set: {} not in {}",
                        Hash(verifier_data_hash.elements),
                        self.vd_set.root(),
                    )));
                }
            }
        }

        let input_statement_offset = self.offset_input_statements();
        // get the input_statements from the self.statements
        let input_statements = &self.statements[input_statement_offset..];
        // 2. get the id out of the public statements, and ensure it is equal to self.id
        if self.id != PodId(calculate_id(&self.public_statements, &self.params)) {
            return Err(Error::pod_id_invalid());
        }
        // 4. Verify type
        // find a ValueOf statement from the public statements with key=KEY_TYPE and check that the
        // value is PodType::MockMainPod
        let type_statement = &self.public_statements[0];
        let type_statement_ok = type_statement.0 == Predicate::Native(NativePredicate::Equal)
            && {
                if let [StatementArg::Key(AnchoredKey { pod_id, ref key }), StatementArg::Literal(pod_type)] =
                    &type_statement.1[..2]
                {
                    pod_id == &SELF
                        && key.hash() == hash_str(KEY_TYPE)
                        && *pod_type == Value::from(PodType::MockMain)
                } else {
                    false
                }
            };
        if !type_statement_ok {
            return Err(Error::not_type_statement());
        }
        // 3. check that all `NewEntry` operations have unique keys
        // (no duplicates)
        let value_ofs_unique = input_statements
            .iter()
            .zip(self.operations.iter())
            .filter_map(|(s, o)| {
                if matches!(o.0, OperationType::Native(NativeOperation::NewEntry)) {
                    match s.1.get(0) {
                        Some(StatementArg::Key(k)) => Some(k),
                        // malformed NewEntry operations are caught in step 5
                        _ => None,
                    }
                } else {
                    None
                }
            })
            .all_unique();
        if !value_ofs_unique {
            return Err(Error::repeated_value_of());
        }

        // 5. verify that all `input_statements` are correctly generated
        // by `self.operations` (where each operation can only access previous statements)
        let statement_check = input_statements
            .iter()
            .enumerate()
            .map(|(i, s)| {
                self.operations[i]
                    .deref(
                        &self.statements[..input_statement_offset + i],
                        &self.merkle_proofs_containers,
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

    fn id(&self) -> PodId {
        self.id
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

    fn serialize_data(&self) -> serde_json::Value {
        let input_signed_pods = self
            .input_signed_pods
            .iter()
            .map(|p| (p.pod_type().0, p.id(), p.serialize_data()))
            .collect();
        let input_recursive_pods = self
            .input_recursive_pods
            .iter()
            .map(|p| {
                (
                    p.pod_type().0,
                    p.params().clone(),
                    p.id(),
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
            input_signed_pods,
            input_recursive_pods,
        })
        .expect("serialization to json")
    }
}

impl RecursivePod for MockMainPod {
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
    // MockMainPods include some internal private state which is necessary
    // for verification. In non-mock Pods, this state will not be necessary,
    // as the public statements can be verified using a ZK proof.
    fn deserialize_data(
        params: Params,
        data: serde_json::Value,
        vd_set: VDSet,
        id: PodId,
    ) -> Result<Box<dyn RecursivePod>> {
        let Data {
            public_statements,
            operations,
            statements,
            merkle_proofs,
            input_signed_pods,
            input_recursive_pods,
        } = serde_json::from_value(data)?;
        let input_signed_pods = input_signed_pods
            .into_iter()
            .map(|(pod_type, id, data)| deserialize_signed_pod(pod_type, id, data))
            .collect::<Result<Vec<_>>>()?;
        let input_recursive_pods = input_recursive_pods
            .into_iter()
            .map(|(pod_type, params, id, vd_set, data)| {
                deserialize_pod(pod_type, params, id, vd_set, data)
            })
            .collect::<Result<Vec<_>>>()?;
        Ok(Box::new(Self {
            params,
            id,
            vd_set,
            input_signed_pods,
            input_recursive_pods,
            public_statements,
            operations,
            statements,
            merkle_proofs_containers: merkle_proofs,
        }))
    }
}

#[cfg(test)]
pub mod tests {
    use std::any::Any;

    use super::*;
    use crate::{
        backends::plonky2::{primitives::ec::schnorr::SecretKey, signedpod::Signer},
        examples::{
            great_boy_pod_full_flow, tickets_pod_full_flow, zu_kyc_pod_builder, zu_kyc_pod_request,
            zu_kyc_sign_pod_builders, MOCK_VD_SET,
        },
        frontend, middleware,
    };

    #[test]
    fn test_mock_main_zu_kyc() -> frontend::Result<()> {
        let params = middleware::Params::default();
        let vd_set = &*MOCK_VD_SET;
        let (gov_id_builder, pay_stub_builder) = zu_kyc_sign_pod_builders(&params);
        let signer = Signer(SecretKey(1u32.into()));
        let gov_id_pod = gov_id_builder.sign(&signer)?;
        let signer = Signer(SecretKey(2u32.into()));
        let pay_stub_pod = pay_stub_builder.sign(&signer)?;
        let kyc_builder = zu_kyc_pod_builder(&params, vd_set, &gov_id_pod, &pay_stub_pod)?;

        let prover = MockProver {};
        let kyc_pod = kyc_builder.prove(&prover)?;
        let pod = (kyc_pod.pod as Box<dyn Any>)
            .downcast::<MockMainPod>()
            .unwrap();

        println!("{:#}", pod);

        pod.verify()?;

        let request = zu_kyc_pod_request(
            gov_id_pod.get("_signer").unwrap(),
            pay_stub_pod.get("_signer").unwrap(),
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
