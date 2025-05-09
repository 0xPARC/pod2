//
// MainPod
//

use std::fmt;

use base64::{prelude::BASE64_STANDARD, Engine};
use serde::{Deserialize, Serialize};

use crate::{
    backends::plonky2::{
        error::{Error, Result},
        mainpod::{
            extract_merkle_proofs, hash_statements, layout_statements, normalize_statement,
            process_private_statements_operations, process_public_statements_operations, Operation,
            Statement,
        },
        primitives::merkletree::MerkleClaimAndProof,
    },
    middleware::{
        self, hash_str, AnchoredKey, DynError, MainPodInputs, NativePredicate, Params, Pod, PodId,
        PodProver, Predicate, StatementArg, KEY_TYPE, SELF,
    },
};

pub struct MockProver {}

impl PodProver for MockProver {
    fn prove(
        &mut self,
        params: &Params,
        inputs: MainPodInputs,
    ) -> Result<Box<dyn Pod>, Box<DynError>> {
        Ok(Box::new(MockMainPod::new(params, inputs)?))
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MockMainPod {
    params: Params,
    id: PodId,
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
}

impl fmt::Display for MockMainPod {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "MockMainPod ({}):", self.id)?;
        // TODO print input signed pods id and type
        // TODO print input main pods id and type
        let offset_input_main_pods = self.offset_input_main_pods();
        let offset_input_statements = self.offset_input_statements();
        let offset_public_statements = self.offset_public_statements();
        for (i, st) in self.statements.iter().enumerate() {
            if (i < self.offset_input_main_pods()) && (i % self.params.max_signed_pod_values == 0) {
                writeln!(
                    f,
                    "  from input SignedPod {}:",
                    i / self.params.max_signed_pod_values
                )?;
            }
            if (i >= offset_input_main_pods)
                && (i < offset_input_statements)
                && ((i - offset_input_main_pods) % self.params.max_public_statements == 0)
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

/// Inputs are sorted as:
/// - SignedPods
/// - MainPods
/// - private Statements
/// - public Statements
impl MockMainPod {
    fn offset_input_main_pods(&self) -> usize {
        self.params.max_input_signed_pods * self.params.max_signed_pod_values
    }
    fn offset_input_statements(&self) -> usize {
        self.offset_input_main_pods()
            + self.params.max_input_main_pods * self.params.max_public_statements
    }
    fn offset_public_statements(&self) -> usize {
        self.offset_input_statements() + self.params.max_priv_statements()
    }

    pub fn new(params: &Params, inputs: MainPodInputs) -> Result<Self> {
        // TODO: Insert a new public statement of ValueOf with `key=KEY_TYPE,
        // value=PodType::MockMainPod`
        let statements = layout_statements(params, &inputs);
        // Extract Merkle proofs and pad.
        let merkle_proofs = extract_merkle_proofs(params, inputs.operations)?;

        let operations = process_private_statements_operations(
            params,
            &statements,
            &merkle_proofs,
            None,
            inputs.operations,
        )?;
        let operations = process_public_statements_operations(params, &statements, operations)?;

        let public_statements =
            statements[statements.len() - params.max_public_statements..].to_vec();

        // get the id out of the public statements
        let id: PodId = PodId(hash_statements(&public_statements, params));

        Ok(Self {
            params: params.clone(),
            id,
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
    pub(crate) fn deserialize(serialized: String) -> Result<Self> {
        let proof = String::from_utf8(BASE64_STANDARD.decode(&serialized)?)
            .map_err(|e| anyhow::anyhow!("Invalid base64 encoding: {}", e))?;
        let pod: MockMainPod = serde_json::from_str(&proof)
            .map_err(|e| anyhow::anyhow!("Failed to parse proof: {}", e))?;

        Ok(pod)
    }

    fn _verify(&self) -> Result<()> {
        // 1. TODO: Verify input pods

        let input_statement_offset = self.offset_input_statements();
        // get the input_statements from the self.statements
        let input_statements = &self.statements[input_statement_offset..];
        // 2. get the id out of the public statements, and ensure it is equal to self.id
        let ids_match = self.id == PodId(hash_statements(&self.public_statements, &self.params));
        // find a ValueOf statement from the public statements with key=KEY_TYPE and check that the
        // value is PodType::MockMainPod
        let has_type_statement = self.public_statements.iter().any(|s| {
            s.0 == Predicate::Native(NativePredicate::ValueOf)
                && !s.1.is_empty()
                && if let StatementArg::Key(AnchoredKey { pod_id, ref key }) = s.1[0] {
                    pod_id == SELF && key.hash() == hash_str(KEY_TYPE)
                } else {
                    false
                }
        });
        // 3. check that all `input_statements` of type `ValueOf` with origin=SELF have unique keys
        // (no duplicates)
        // TODO: Instead of doing this, do a uniqueness check when verifying the output of a
        // `NewValue` operation.
        let value_ofs_unique = {
            let key_id_pairs = input_statements
                .iter()
                .enumerate()
                .map(|(i, s)| {
                    (
                        // Separate private from public statements.
                        if i < self.params.max_priv_statements() {
                            0
                        } else {
                            1
                        },
                        s,
                    )
                })
                .filter(|(_, s)| s.0 == Predicate::Native(NativePredicate::ValueOf))
                .flat_map(|(i, s)| {
                    if let StatementArg::Key(ak) = &s.1[0] {
                        vec![(i, ak.pod_id, ak.key.hash())]
                    } else {
                        vec![]
                    }
                })
                .collect::<Vec<_>>();
            !(0..key_id_pairs.len() - 1).any(|i| key_id_pairs[i + 1..].contains(&key_id_pairs[i]))
        };
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
}

impl Pod for MockMainPod {
    fn verify(&self) -> Result<(), Box<DynError>> {
        Ok(self._verify()?)
    }
    fn id(&self) -> PodId {
        self.id
    }
    fn pub_statements(&self) -> Vec<middleware::Statement> {
        // return the public statements, where when origin=SELF is replaced by origin=self.id()
        // By convention we expect the KEY_TYPE to be the first statement
        self.statements
            .iter()
            .skip(self.offset_public_statements())
            .cloned()
            .map(|statement| normalize_statement(&statement, self.id()))
            .collect()
    }

    fn serialized_proof(&self) -> String {
        BASE64_STANDARD.encode(serde_json::to_string(self).unwrap())
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
        middleware::{self},
    };

    #[test]
    fn test_mock_main_zu_kyc() -> frontend::Result<()> {
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
        let params = middleware::Params::default();
        let great_boy_builder = great_boy_pod_full_flow()?;

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
