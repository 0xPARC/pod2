//
// MainPod
//

use std::fmt;

use itertools::Itertools;
use serde::{Deserialize, Serialize};

use crate::{
    backends::plonky2::{
        basetypes::{Proof, VerifierOnlyCircuitData},
        error::{Error, Result},
        mainpod::{
            calculate_id, extract_merkle_proofs, layout_statements,
            process_private_statements_operations, process_public_statements_operations, Operation,
            Statement,
        },
        primitives::merkletree::MerkleClaimAndProof,
    },
    middleware::{
        self, hash_str, AnchoredKey, DynError, Hash, MainPodInputs, NativeOperation,
        NativePredicate, OperationType, Params, Pod, PodId, PodProver, PodType, Predicate,
        RecursivePod, StatementArg, VDSet, KEY_TYPE, SELF,
    },
};

pub struct MockProver {}

impl PodProver for MockProver {
    fn prove(
        &self,
        params: &Params,
        _vd_set: &VDSet,
        inputs: MainPodInputs,
    ) -> Result<Box<dyn RecursivePod>, Box<DynError>> {
        Ok(Box::new(MockMainPod::new(params, inputs)?))
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MockMainPod {
    params: Params,
    id: PodId,
    vds_root: Hash,
    //   input_signed_pods: Vec<Box<dyn Pod>>,
    //   input_main_pods: Vec<Box<dyn Pod>>,
    // New statements introduced by this pod
    //   input_statements: Vec<Statement>,
    public_statements: Vec<Statement>,
    operations: Vec<Operation>,
    // All statements (inherited + new)
    statements: Vec<Statement>,
    // All Merkle proofs
    // TODO: Use a backend-specific representation
    merkle_proofs: Vec<MerkleClaimAndProof>,
    // TODO: Add input pods
}

impl fmt::Display for MockMainPod {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "MockMainPod ({}):", self.id)?;
        // TODO print input signed pods id and type
        // TODO print input main pods id and type
        let offset_input_signed_pods = Self::offset_input_signed_pods();
        let offset_input_main_pods = self.offset_input_main_pods();
        let offset_input_statements = self.offset_input_statements();
        let offset_public_statements = self.offset_public_statements();
        for (i, st) in self.statements.iter().enumerate() {
            if (i >= offset_input_signed_pods && i < offset_input_main_pods)
                && ((i - offset_input_signed_pods) % self.params.max_signed_pod_values == 0)
            {
                writeln!(
                    f,
                    "  from input SignedPod {}:",
                    i / self.params.max_signed_pod_values
                )?;
            }
            if (i >= offset_input_main_pods)
                && (i < offset_input_statements)
                && ((i - offset_input_main_pods) % self.params.max_input_pods_public_statements
                    == 0)
            {
                writeln!(
                    f,
                    "  from input MainPod {}:",
                    (i - offset_input_main_pods) / self.params.max_signed_pod_values
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
    fn offset_input_main_pods(&self) -> usize {
        Self::offset_input_signed_pods()
            + self.params.max_input_signed_pods * self.params.max_signed_pod_values
    }
    fn offset_input_statements(&self) -> usize {
        self.offset_input_main_pods()
            + self.params.max_input_recursive_pods * self.params.max_input_pods_public_statements
    }
    fn offset_public_statements(&self) -> usize {
        self.offset_input_statements() + self.params.max_priv_statements()
    }

    pub fn new(params: &Params, inputs: MainPodInputs) -> Result<Self> {
        // TODO: Insert a new public statement of ValueOf with `key=KEY_TYPE,
        // value=PodType::MockMainPod`
        let (statements, public_statements) = layout_statements(params, true, &inputs)?;
        // Extract Merkle proofs and pad.
        let merkle_proofs = extract_merkle_proofs(params, inputs.operations, inputs.statements)?;

        let operations = process_private_statements_operations(
            params,
            &statements,
            &merkle_proofs,
            None,
            inputs.operations,
        )?;
        let operations = process_public_statements_operations(params, &statements, operations)?;

        // get the id out of the public statements
        let id: PodId = PodId(calculate_id(&public_statements, params));

        Ok(Self {
            params: params.clone(),
            id,
            vds_root: inputs.vds_set.root(),
            //  input_signed_pods,
            //  input_main_pods,
            //  input_statements,
            public_statements,
            statements,
            operations,
            merkle_proofs,
        })
    }

    // MockMainPods include some internal private state which is necessary
    // for verification. In non-mock Pods, this state will not be necessary,
    // as the public statements can be verified using a ZK proof.
    pub(crate) fn deserialize(
        params: Params,
        id: PodId,
        vds_root: Hash,
        data: serde_json::Value,
    ) -> Result<Box<dyn RecursivePod>> {
        let Data {
            public_statements,
            operations,
            statements,
            merkle_proofs,
        } = serde_json::from_value(data)?;
        Ok(Box::new(Self {
            params,
            id,
            vds_root,
            public_statements,
            operations,
            statements,
            merkle_proofs,
        }))
    }

    fn _verify(&self) -> Result<()> {
        // 1. TODO: Verify input pods

        let input_statement_offset = self.offset_input_statements();
        // get the input_statements from the self.statements
        let input_statements = &self.statements[input_statement_offset..];
        // 2. get the id out of the public statements, and ensure it is equal to self.id
        let ids_match = self.id == PodId(calculate_id(&self.public_statements, &self.params));
        // find a ValueOf statement from the public statements with key=KEY_TYPE and check that the
        // value is PodType::MockMainPod
        let has_type_statement = self.public_statements.iter().any(|s| {
            s.0 == Predicate::Native(NativePredicate::Equal) && {
                if let [StatementArg::Key(AnchoredKey { pod_id, ref key }), StatementArg::Literal(_)] = &s.1[..2] {
                    pod_id == &SELF && key.hash() == hash_str(KEY_TYPE)
                } else {
                    false
                }
        }});
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
        // 4. TODO: Verify type

        // 5. verify that all `input_statements` are correctly generated
        // by `self.operations` (where each operation can only access previous statements)
        let statement_check = input_statements
            .iter()
            .enumerate()
            .map(|(i, s)| {
                self.operations[i]
                    .deref(
                        &self.statements[..input_statement_offset + i],
                        &self.merkle_proofs,
                    )
                    .unwrap()
                    .check_and_log(&self.params, &s.clone().try_into().unwrap())
            })
            .collect::<Result<Vec<_>, middleware::Error>>()
            .unwrap();
        if !ids_match {
            return Err(Error::pod_id_invalid());
        }
        if !has_type_statement {
            return Err(Error::not_type_statement());
        }
        if !value_ofs_unique {
            return Err(Error::repeated_value_of());
        }
        if !statement_check.iter().all(|b| *b) {
            return Err(Error::statement_not_check());
        }
        Ok(())
    }

    pub fn params(&self) -> &Params {
        &self.params
    }
}

impl Pod for MockMainPod {
    fn params(&self) -> &Params {
        &self.params
    }
    fn verify(&self) -> Result<(), Box<DynError>> {
        Ok(self._verify()?)
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
        serde_json::to_value(Data {
            public_statements: self.public_statements.clone(),
            operations: self.operations.clone(),
            statements: self.statements.clone(),
            merkle_proofs: self.merkle_proofs.clone(),
        })
        .expect("serialization to json")
    }
}

impl RecursivePod for MockMainPod {
    fn verifier_data(&self) -> VerifierOnlyCircuitData {
        panic!("MockMainPod can't be verified in a recursive MainPod circuit");
    }
    fn proof(&self) -> Proof {
        panic!("MockMainPod can't be verified in a recursive MainPod circuit");
    }
    fn vds_root(&self) -> Hash {
        self.vds_root
    }
}

#[cfg(test)]
pub mod tests {
    use std::any::Any;

    use super::*;
    use crate::{
        backends::plonky2::mock::signedpod::MockSigner,
        examples::{
            great_boy_pod_full_flow, tickets_pod_full_flow, zu_kyc_pod_builder,
            zu_kyc_sign_pod_builders,
        },
        frontend,
        middleware::{self, DEFAULT_VD_SET},
    };

    #[test]
    fn test_mock_main_zu_kyc() -> frontend::Result<()> {
        let params = middleware::Params::default();
        let vd_set = &*DEFAULT_VD_SET;
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
        let kyc_builder = zu_kyc_pod_builder(
            &params,
            &vd_set,
            &gov_id_pod,
            &pay_stub_pod,
            &sanction_list_pod,
        )?;

        let mut prover = MockProver {};
        let kyc_pod = kyc_builder.prove(&mut prover, &params)?;
        let pod = (kyc_pod.pod as Box<dyn Any>)
            .downcast::<MockMainPod>()
            .unwrap();

        println!("{:#}", pod);

        pod.verify()?; // TODO
                       // println!("id: {}", pod.id());
                       // println!("pub_statements: {:?}", pod.pub_statements());
        Ok(())
    }

    #[test]
    fn test_mock_main_great_boy() -> frontend::Result<()> {
        let (params, great_boy_builder) = great_boy_pod_full_flow()?;

        let mut prover = MockProver {};
        let great_boy_pod = great_boy_builder.prove(&mut prover, &params)?;
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
        let tickets_builder = tickets_pod_full_flow()?;
        let mut prover = MockProver {};
        let proof_pod = tickets_builder.prove(&mut prover, &params)?;
        let pod = (proof_pod.pod as Box<dyn Any>)
            .downcast::<MockMainPod>()
            .unwrap();

        println!("{}", pod);
        pod.verify()?;

        Ok(())
    }
}
