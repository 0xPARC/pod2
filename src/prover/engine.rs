use super::types::*;
use crate::frontend::{AnchoredKey, Origin, PodClass, Value};
use crate::middleware::{NativeOperation, SELF};
use crate::{MainPod, SignedPod};
use ascent::ascent;

use super::types::WildcardStatement;

// Supports arrays and sets, returns false for other types
fn check_contains(container: &Value, contained: &Value) -> bool {
    match (container, contained) {
        // For arrays, check if the contained value is an element
        (Value::Array(arr), value) => {
            // Check each element in the array using the iterator
            for (_, elem) in arr.middleware_array().iter() {
                if elem == &value.into() {
                    return true;
                }
            }
            false
        }

        // For sets, check if the contained value is a member
        (Value::Set(set), value) => set
            .middleware_set()
            .contains(&value.into())
            .unwrap_or(false),

        // For other types, containment is not defined
        _ => false,
    }
}

// Main deduction engine that handles proof generation
pub struct DeductionEngine {
    prog: AscentProgram,
}

impl DeductionEngine {
    pub fn new() -> Self {
        Self {
            prog: AscentProgram::default(),
        }
    }

    // Reset the program's state
    pub fn reset(&mut self) {
        self.prog = AscentProgram::default();
    }

    // Add a known fact to the engine
    pub fn add_fact(&mut self, fact: ProvableStatement) {
        self.prog.known_statement.push((fact,));
    }

    // All all of the statements from a signed pod
    pub fn add_signed_pod(&mut self, pod: SignedPod) {
        for (key, value) in pod.kvs {
            self.add_fact(ProvableStatement::ValueOf(
                AnchoredKey {
                    origin: Origin {
                        pod_class: PodClass::Signed,
                        pod_id: pod.pod.id(),
                    },
                    key: key.to_string(),
                },
                value.into(),
            ));
        }
    }

    // Add all of the statements from a main pod
    pub fn add_main_pod(&mut self, pod: MainPod) {
        for stmt in pod.public_statements {
            self.add_fact(stmt.into());
        }
    }

    // Set the target statement we're trying to prove
    pub fn set_target(&mut self, target: WildcardTargetStatement) {
        let target = match target {
            WildcardTargetStatement::Equal(ak, arg) => {
                if let WildcardStatementArg::Key(key) = arg {
                    WildcardStatement::Equal(ak, key)
                } else if let WildcardStatementArg::Literal(v) = arg {
                    let new_ak = AnchoredKey {
                        origin: Origin {
                            pod_class: PodClass::Main,
                            pod_id: SELF,
                        },
                        key: "value_of_0".to_string(),
                    };
                    self.add_fact(ProvableStatement::ValueOf(new_ak.clone(), v));
                    WildcardStatement::Equal(ak, new_ak.clone())
                } else {
                    panic!("Invalid wildcard statement argument");
                }
            }
            WildcardTargetStatement::NotEqual(ak, arg) => {
                if let WildcardStatementArg::Key(key) = arg {
                    WildcardStatement::NotEqual(ak, key)
                } else if let WildcardStatementArg::Literal(v) = arg {
                    let new_ak = AnchoredKey {
                        origin: Origin {
                            pod_class: PodClass::Main,
                            pod_id: SELF,
                        },
                        key: "value_of_0".to_string(),
                    };
                    self.add_fact(ProvableStatement::ValueOf(new_ak.clone(), v));
                    WildcardStatement::NotEqual(ak, new_ak.clone())
                } else {
                    panic!("Invalid wildcard statement argument");
                }
            }
            WildcardTargetStatement::Gt(ak, arg) => {
                if let WildcardStatementArg::Key(key) = arg {
                    WildcardStatement::Gt(ak, key)
                } else if let WildcardStatementArg::Literal(v) = arg {
                    let new_ak = AnchoredKey {
                        origin: Origin {
                            pod_class: PodClass::Main,
                            pod_id: SELF,
                        },
                        key: "value_of_0".to_string(),
                    };
                    self.add_fact(ProvableStatement::ValueOf(new_ak.clone(), v));
                    WildcardStatement::Gt(ak, new_ak.clone())
                } else {
                    panic!("Invalid wildcard statement argument");
                }
            }
            WildcardTargetStatement::Lt(ak, arg) => {
                if let WildcardStatementArg::Key(key) = arg {
                    WildcardStatement::Lt(ak, key)
                } else if let WildcardStatementArg::Literal(v) = arg {
                    let new_ak = AnchoredKey {
                        origin: Origin {
                            pod_class: PodClass::Main,
                            pod_id: SELF,
                        },
                        key: "value_of_0".to_string(),
                    };
                    self.add_fact(ProvableStatement::ValueOf(new_ak.clone(), v));
                    WildcardStatement::Lt(ak, new_ak.clone())
                } else {
                    panic!("Invalid wildcard statement argument");
                }
            }
            WildcardTargetStatement::Contains(ak, arg) => {
                if let WildcardStatementArg::Key(key) = arg {
                    WildcardStatement::Contains(ak, key)
                } else if let WildcardStatementArg::Literal(v) = arg {
                    let new_ak = AnchoredKey {
                        origin: Origin {
                            pod_class: PodClass::Main,
                            pod_id: SELF,
                        },
                        key: "value_of_0".to_string(),
                    };
                    self.add_fact(ProvableStatement::ValueOf(new_ak.clone(), v));
                    WildcardStatement::Contains(ak, new_ak.clone())
                } else {
                    panic!("Invalid wildcard statement argument");
                }
            }
            WildcardTargetStatement::NotContains(ak, arg) => {
                if let WildcardStatementArg::Key(key) = arg {
                    WildcardStatement::NotContains(ak, key)
                } else if let WildcardStatementArg::Literal(v) = arg {
                    let new_ak = AnchoredKey {
                        origin: Origin {
                            pod_class: PodClass::Main,
                            pod_id: SELF,
                        },
                        key: "value_of_0".to_string(),
                    };
                    self.add_fact(ProvableStatement::ValueOf(new_ak.clone(), v));
                    WildcardStatement::NotContains(ak, new_ak.clone())
                } else {
                    panic!("Invalid wildcard statement argument");
                }
            }
            WildcardTargetStatement::SumOf(result, op1, op2) => {
                let op1_key = match op1 {
                    WildcardStatementArg::Key(key) => key,
                    WildcardStatementArg::Literal(v) => {
                        let new_ak = AnchoredKey {
                            origin: Origin {
                                pod_class: PodClass::Main,
                                pod_id: SELF,
                            },
                            key: "value_of_sum1".to_string(),
                        };
                        self.add_fact(ProvableStatement::ValueOf(new_ak.clone(), v));
                        new_ak
                    }
                };
                let op2_key = match op2 {
                    WildcardStatementArg::Key(key) => key,
                    WildcardStatementArg::Literal(v) => {
                        let new_ak = AnchoredKey {
                            origin: Origin {
                                pod_class: PodClass::Main,
                                pod_id: SELF,
                            },
                            key: "value_of_sum2".to_string(),
                        };
                        self.add_fact(ProvableStatement::ValueOf(new_ak.clone(), v));
                        new_ak
                    }
                };
                WildcardStatement::SumOf(result, op1_key, op2_key)
            }
            WildcardTargetStatement::ProductOf(result, op1, op2) => {
                let op1_key = match op1 {
                    WildcardStatementArg::Key(key) => key,
                    WildcardStatementArg::Literal(v) => {
                        let new_ak = AnchoredKey {
                            origin: Origin {
                                pod_class: PodClass::Main,
                                pod_id: SELF,
                            },
                            key: "value_of_prod1".to_string(),
                        };
                        self.add_fact(ProvableStatement::ValueOf(new_ak.clone(), v));
                        new_ak
                    }
                };
                let op2_key = match op2 {
                    WildcardStatementArg::Key(key) => key,
                    WildcardStatementArg::Literal(v) => {
                        let new_ak = AnchoredKey {
                            origin: Origin {
                                pod_class: PodClass::Main,
                                pod_id: SELF,
                            },
                            key: "value_of_prod2".to_string(),
                        };
                        self.add_fact(ProvableStatement::ValueOf(new_ak.clone(), v));
                        new_ak
                    }
                };
                WildcardStatement::ProductOf(result, op1_key, op2_key)
            }
            WildcardTargetStatement::MaxOf(result, op1, op2) => {
                let op1_key = match op1 {
                    WildcardStatementArg::Key(key) => key,
                    WildcardStatementArg::Literal(v) => {
                        let new_ak = AnchoredKey {
                            origin: Origin {
                                pod_class: PodClass::Main,
                                pod_id: SELF,
                            },
                            key: "value_of_max1".to_string(),
                        };
                        self.add_fact(ProvableStatement::ValueOf(new_ak.clone(), v));
                        new_ak
                    }
                };
                let op2_key = match op2 {
                    WildcardStatementArg::Key(key) => key,
                    WildcardStatementArg::Literal(v) => {
                        let new_ak = AnchoredKey {
                            origin: Origin {
                                pod_class: PodClass::Main,
                                pod_id: SELF,
                            },
                            key: "value_of_max2".to_string(),
                        };
                        self.add_fact(ProvableStatement::ValueOf(new_ak.clone(), v));
                        new_ak
                    }
                };
                WildcardStatement::MaxOf(result, op1_key, op2_key)
            }
        };
        self.prog.target_statement = vec![(target,)];
    }

    // Run the deduction engine and return all proofs found
    pub fn prove(&mut self) -> Vec<(ProvableStatement, DeductionChain)> {
        self.prog.run();
        self.prog.can_prove.clone()
    }

    // Print a human-readable proof chain
    pub fn print_proof(&self, statement: ProvableStatement, chain: DeductionChain) {
        println!("\nProved: {}", statement);
        if chain.is_empty() {
            println!("This statement was directly known (no deduction needed)");
            return;
        }

        println!("\nProof steps:");
        for (step, (op_code, inputs, output)) in chain.iter().enumerate() {
            println!("\nStep {}:", step + 1);
            println!("Operation: {}", operation_name(*op_code));
            println!("From:");
            for input in inputs {
                println!("  - {}", input);
            }
            println!("Deduced:");
            println!("  => {}", output);
        }
    }

    pub fn prove_multiple(
        &mut self,
        targets: Vec<WildcardTargetStatement>,
    ) -> Vec<(ProvableStatement, DeductionChain)> {
        let mut all_proofs = Vec::new();
        let mut remaining_targets = targets;

        // Store original known statements before we start
        let original_known_statements: Vec<ProvableStatement> = self
            .prog
            .known_statement
            .iter()
            .map(|(stmt,)| stmt.clone())
            .collect();

        while !remaining_targets.is_empty() {
            let mut new_remaining = Vec::new();
            let mut proved_something = false;

            println!(
                "\nAttempting to prove {} remaining targets",
                remaining_targets.len()
            );
            // Try to prove each remaining target
            for (i, target) in remaining_targets.iter().enumerate() {
                println!("\nTrying to prove target {}: {:?}", i, target);

                // Reset the program's state before each attempt
                self.reset();

                // Re-add original known statements
                for stmt in &original_known_statements {
                    self.add_fact(stmt.clone());
                }

                // Re-add all previously proven facts
                for (_, _, output) in all_proofs
                    .iter()
                    .flat_map(|(_, chain): &(ProvableStatement, DeductionChain)| chain.iter())
                {
                    self.add_fact(output.clone());
                }

                self.set_target(target.clone());

                self.prog.run();
                if let Some(proof) = self.prog.can_prove.first().cloned() {
                    println!("Successfully proved target {}: {:?}", i, proof.0);
                    // Successfully proved this target
                    // Add all intermediate steps in the proof chain as facts
                    for (_, _, output) in &proof.1 {
                        println!("Adding intermediate fact: {:?}", output);
                        self.add_fact(output.clone());
                    }
                    // Add the final proven statement as a fact
                    println!("Adding final fact: {:?}", proof.0);
                    self.add_fact(proof.0.clone());
                    all_proofs.push(proof);
                    proved_something = true;
                } else {
                    println!("Could not prove target {} yet", i);
                    // Couldn't prove it yet, keep it for next round
                    new_remaining.push(target.clone());
                }
            }

            // If we didn't prove anything new this round, we're stuck
            if !proved_something {
                println!("\nNo new proofs found this round, stopping");
                // These statements are unprovable with current knowledge
                break;
            }

            remaining_targets = new_remaining;
        }

        println!("\nFinal proofs:");
        for (i, proof) in all_proofs.iter().enumerate() {
            println!("Proof {}: {:?}", i, proof.0);
        }
        all_proofs
    }
}

ascent! {
    // Core relations that track our knowledge and goals
    relation known_statement(ProvableStatement);  // Statements we know to be true
    relation target_statement(WildcardStatement);  // The statement we're trying to prove
    relation can_prove(ProvableStatement, DeductionChain);  // Statements we can prove with their proof chains
    relation known_value(AnchoredKey, Value);  // Values we know for specific keys
    relation known_int_value(AnchoredKey, Value);  // Values we know to be integers
    relation known_equal(AnchoredKey, AnchoredKey);  // Known equality relationships
    relation known_gt(AnchoredKey, AnchoredKey);  // Known greater-than relationships
    relation known_lt(AnchoredKey, AnchoredKey);  // Known less-than relationships
    relation known_neq(AnchoredKey, AnchoredKey);  // Known not-equal relationships
    relation known_contains(AnchoredKey, AnchoredKey);  // Known contains relationships
    relation reachable_equal(AnchoredKey, AnchoredKey, DeductionChain);  // Equality relationships we can prove through chains
    relation connected_to_target2(AnchoredKey, AnchoredKey, DeductionChain);  // Chains that connect to our target statement (2 operands)
    relation connected_to_target3(AnchoredKey, AnchoredKey, AnchoredKey, DeductionChain);  // Chains that connect to our target statement (3 operands)

    // Base case: directly match known statements with wildcard targets
    can_prove(stmt, chain) <--
        target_statement(wild_stmt),
        known_statement(known_stmt),
        if let WildcardStatement::Equal(wild_key, concrete_key) = wild_stmt,
        if let ProvableStatement::Equal(known_key, known_concrete) = known_stmt,
        if wild_key.matches(&known_key) && concrete_key == known_concrete,
        let stmt = known_stmt.clone(),
        let chain = vec![];

    // Prove equality through chains of known equalities
    can_prove(stmt, chain) <--
        target_statement(target_stmt),
        if let WildcardStatement::Equal(wild_key, concrete_key) = target_stmt,
        connected_to_target2(found_key, match_key, chain),
        if wild_key.matches(&found_key),
        let stmt = ProvableStatement::Equal(found_key.clone(), concrete_key.clone());

    // Prove greater-than relationships through chains
    can_prove(stmt, chain) <--
        target_statement(target_stmt),
        if let WildcardStatement::Gt(wild_key, concrete_key) = target_stmt,
        connected_to_target2(found_key, match_key, chain),
        if wild_key.matches(&found_key),
        let stmt = ProvableStatement::Gt(found_key.clone(), concrete_key.clone());

    // Prove less-than relationships through chains
    can_prove(stmt, chain) <--
        target_statement(target_stmt),
        if let WildcardStatement::Lt(wild_key, concrete_key) = target_stmt,
        connected_to_target2(found_key, match_key, chain),
        if wild_key.matches(&found_key),
        let stmt = ProvableStatement::Lt(found_key.clone(), concrete_key.clone());

    // Prove not-equal relationships through chains
    can_prove(stmt, chain) <--
        target_statement(target_stmt),
        if let WildcardStatement::NotEqual(wild_key, concrete_key) = target_stmt,
        connected_to_target2(found_key, match_key, chain),
        if wild_key.matches(&found_key),
        let stmt = ProvableStatement::NotEqual(found_key.clone(), concrete_key.clone());

    // Prove contains relationships through chains
    can_prove(stmt, chain) <--
        target_statement(target_stmt),
        if let WildcardStatement::Contains(wild_key, concrete_key) = target_stmt,
        connected_to_target2(found_key, match_key, chain),
        if wild_key.matches(&found_key),
        let stmt = ProvableStatement::Contains(found_key.clone(), concrete_key.clone());

    // Prove not-contains relationships through chains
    can_prove(stmt, chain) <--
        target_statement(target_stmt),
        if let WildcardStatement::NotContains(wild_key, concrete_key) = target_stmt,
        connected_to_target2(found_key, match_key, chain),
        if wild_key.matches(&found_key),
        let stmt = ProvableStatement::NotContains(found_key.clone(), concrete_key.clone());

    // Prove arithmetic relationships through chains
    can_prove(stmt, chain) <--
        target_statement(target_stmt),
        if let WildcardStatement::SumOf(result_key, op1_key, op2_key) = target_stmt,
        connected_to_target3(found_result, found_op1, found_op2, chain),
        if result_key.matches(&found_result),
        let stmt = ProvableStatement::SumOf(found_result.clone(), op1_key.clone(), op2_key.clone());

    can_prove(stmt, chain) <--
        target_statement(target_stmt),
        if let WildcardStatement::ProductOf(result_key, op1_key, op2_key) = target_stmt,
        connected_to_target3(found_result, found_op1, found_op2, chain),
        if result_key.matches(&found_result),
        let stmt = ProvableStatement::ProductOf(found_result.clone(), op1_key.clone(), op2_key.clone());

    can_prove(stmt, chain) <--
        target_statement(target_stmt),
        if let WildcardStatement::MaxOf(result_key, op1_key, op2_key) = target_stmt,
        connected_to_target3(found_result, found_op1, found_op2, chain),
        if result_key.matches(&found_result),
        let stmt = ProvableStatement::MaxOf(found_result.clone(), op1_key.clone(), op2_key.clone());

    // Extract value assignments from known statements
    known_value(ak, v) <--
        known_statement(stmt),
        if let ProvableStatement::ValueOf(ak, v) = stmt;

    known_int_value(ak, v) <--
        known_value(ak, v),
        if let Value::Int(_) = v;

    // Extract equality relationships from known statements
    known_equal(ak1, ak2) <--
        known_statement(stmt),
        if let ProvableStatement::Equal(ak1, ak2) = stmt;

    // Extract greater-than relationships from known statements
    known_gt(ak1, ak2) <--
        known_statement(stmt),
        if let ProvableStatement::Gt(ak1, ak2) = stmt;

    // Extract less-than relationships from known statements
    known_lt(ak1, ak2) <--
        known_statement(stmt),
        if let ProvableStatement::Lt(ak1, ak2) = stmt;

    // Extract not-equal relationships from known statements
    known_neq(ak1, ak2) <--
        known_statement(stmt),
        if let ProvableStatement::NotEqual(ak1, ak2) = stmt;

    // Extract contains relationships from known statements
    known_contains(ak1, ak2) <--
        known_statement(stmt),
        if let ProvableStatement::Contains(ak1, ak2) = stmt;

    // Base case: directly known equalities are reachable with empty chain
    reachable_equal(x, y, chain) <--
        known_equal(x, y),
        let chain = vec![];

    // Also add the reverse direction for known equalities (equality is symmetric)
    reachable_equal(y, x, chain) <--
        known_equal(x, y),
        let chain = vec![];

    // Add equality from values to reachable_equal
    reachable_equal(x, y, chain) <--
        known_value(x, v1),
        known_value(y, v2),
        if v1 == v2,
        let chain = vec![(
            NativeOperation::EqualFromEntries as u8,
            vec![
                ProvableStatement::ValueOf(x.clone(), v1.clone()),
                ProvableStatement::ValueOf(y.clone(), v2.clone())
            ],
            ProvableStatement::Equal(x.clone(), y.clone())
        )];

    // Build chains of equalities through transitivity (if a=b and b=c, then a=c)
    reachable_equal(x, z, chain) <--
        reachable_equal(x, y, chain1),
        known_equal(y, z),
        let chain = {
            let mut chain = chain1.clone();
            chain.push((
                NativeOperation::TransitiveEqualFromStatements as u8,
                vec![
                    ProvableStatement::Equal(x.clone(), y.clone()),
                    ProvableStatement::Equal(y.clone(), z.clone())
                ],
                ProvableStatement::Equal(x.clone(), z.clone())
            ));
            chain
        };

    // Find chains that connect to our target key for equality statements
    connected_to_target2(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::Equal(wild_key, concrete_key) = stmt,
        reachable_equal(x, y, chain),
        if y == concrete_key;

    // Prove equality from values (if two keys have the same value, they're equal)
    connected_to_target2(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::Equal(wild_key, concrete_key) = stmt,
        known_value(found_key, v1),
        known_value(match_key, v2),
        if wild_key.matches(&found_key) && match_key == concrete_key,
        if v1 == v2,
        let x = found_key.clone(),
        let y = match_key.clone(),
        let chain = vec![(
            NativeOperation::EqualFromEntries as u8,
            vec![
                ProvableStatement::ValueOf(x.clone(), v1.clone()),
                ProvableStatement::ValueOf(y.clone(), v2.clone())
            ],
            ProvableStatement::Equal(x.clone(), y.clone())
        )];

    // Find chains for greater-than relationships:
    // 1. Direct value comparisons (e.g., 10 > 5)
    connected_to_target2(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::Gt(wild_key, concrete_key) = stmt,
        known_int_value(found_key, v1),
        known_int_value(match_key, v2),
        if wild_key.matches(&found_key) && match_key == concrete_key,
        if let Value::Int(i1) = v1,
        if let Value::Int(i2) = v2,
        if i1 > i2,
        let x = found_key.clone(),
        let y = match_key.clone(),
        let chain = vec![(
            NativeOperation::GtFromEntries as u8,
            vec![
                ProvableStatement::ValueOf(x.clone(), v1.clone()),
                ProvableStatement::ValueOf(y.clone(), v2.clone())
            ],
            ProvableStatement::Gt(x.clone(), y.clone())
        )];

    // 2. Existing greater-than statements
    connected_to_target2(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::Gt(wild_key, concrete_key) = stmt,
        known_statement(known_stmt),
        if let ProvableStatement::Gt(found_key, match_key) = known_stmt,
        if wild_key.matches(&found_key) && match_key == concrete_key,
        let x = found_key.clone(),
        let y = match_key.clone(),
        let chain = vec![];

    // Find chains for less-than relationships:
    // 1. Direct value comparisons (e.g., 5 < 10)
    connected_to_target2(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::Lt(wild_key, concrete_key) = stmt,
        known_int_value(found_key, v1),
        known_int_value(match_key, v2),
        if wild_key.matches(&found_key) && match_key == concrete_key,
        if let Value::Int(i1) = v1,
        if let Value::Int(i2) = v2,
        if i1 < i2,
        let x = found_key.clone(),
        let y = match_key.clone(),
        let chain = vec![(
            NativeOperation::LtFromEntries as u8,
            vec![
                ProvableStatement::ValueOf(x.clone(), v1.clone()),
                ProvableStatement::ValueOf(y.clone(), v2.clone())
            ],
            ProvableStatement::Lt(x.clone(), y.clone())
        )];

    // 2. Existing less-than statements
    connected_to_target2(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::Lt(wild_key, concrete_key) = stmt,
        known_statement(known_stmt),
        if let ProvableStatement::Lt(found_key, match_key) = known_stmt,
        if wild_key.matches(&found_key) && match_key == concrete_key,
        let x = found_key.clone(),
        let y = match_key.clone(),
        let chain = vec![];

    // Find chains for not-equal relationships:
    // 1. Converting greater-than to not-equal (if a > b, then a ≠ b)
    connected_to_target2(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::NotEqual(wild_key, concrete_key) = stmt,
        known_statement(known_stmt),
        if let ProvableStatement::Gt(found_key, match_key) = known_stmt,
        if wild_key.matches(&found_key) && match_key == concrete_key,
        let x = found_key.clone(),
        let y = match_key.clone(),
        let chain = vec![(
            NativeOperation::GtToNotEqual as u8,
            vec![ProvableStatement::Gt(x.clone(), y.clone())],
            ProvableStatement::NotEqual(x.clone(), y.clone())
        )];

    // 2. Converting less-than to not-equal (if a < b, then a ≠ b)
    connected_to_target2(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::NotEqual(wild_key, concrete_key) = stmt,
        known_statement(known_stmt),
        if let ProvableStatement::Lt(found_key, match_key) = known_stmt,
        if wild_key.matches(&found_key) && match_key == concrete_key,
        let x = found_key.clone(),
        let y = match_key.clone(),
        let chain = vec![(
            NativeOperation::LtToNotEqual as u8,
            vec![ProvableStatement::Lt(x.clone(), y.clone())],
            ProvableStatement::NotEqual(x.clone(), y.clone())
        )];

    // 3. Existing not-equal statements
    connected_to_target2(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::NotEqual(wild_key, concrete_key) = stmt,
        known_statement(known_stmt),
        if let ProvableStatement::NotEqual(found_key, match_key) = known_stmt,
        if wild_key.matches(&found_key) && match_key == concrete_key,
        let x = found_key.clone(),
        let y = match_key.clone(),
        let chain = vec![];

    // Find chains for contains relationships:
    // 1. Direct value comparisons (checking if a value is in an array or set)
    connected_to_target2(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::Contains(wild_key, concrete_key) = stmt,
        known_value(found_key, v1),
        known_value(match_key, v2),
        if wild_key.matches(&found_key) && match_key == concrete_key,
        if check_contains(&v1, &v2),
        let x = found_key.clone(),
        let y = match_key.clone(),
        let chain = vec![(
            NativeOperation::ContainsFromEntries as u8,
            vec![
                ProvableStatement::ValueOf(x.clone(), v1.clone()),
                ProvableStatement::ValueOf(y.clone(), v2.clone())
            ],
            ProvableStatement::Contains(x.clone(), y.clone())
        )];

    // 2. Existing contains statements
    connected_to_target2(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::Contains(wild_key, concrete_key) = stmt,
        known_statement(known_stmt),
        if let ProvableStatement::Contains(found_key, match_key) = known_stmt,
        if wild_key.matches(&found_key) && match_key == concrete_key,
        let x = found_key.clone(),
        let y = match_key.clone(),
        let chain = vec![];

    // Find chains for not-contains relationships:
    // 1. Direct value comparisons (checking if a value is not in an array or set)
    connected_to_target2(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::NotContains(wild_key, concrete_key) = stmt,
        known_value(found_key, v1),
        known_value(match_key, v2),
        if wild_key.matches(&found_key) && match_key == concrete_key,
        if !check_contains(&v1, &v2),
        let x = found_key.clone(),
        let y = match_key.clone(),
        let chain = vec![(
            NativeOperation::NotContainsFromEntries as u8,
            vec![
                ProvableStatement::ValueOf(x.clone(), v1.clone()),
                ProvableStatement::ValueOf(y.clone(), v2.clone())
            ],
            ProvableStatement::NotContains(x.clone(), y.clone())
        )];

    // 2. Existing not-contains statements
    connected_to_target2(x, y, chain) <--
        target_statement(stmt),
        if let WildcardStatement::NotContains(wild_key, concrete_key) = stmt,
        known_statement(known_stmt),
        if let ProvableStatement::NotContains(found_key, match_key) = known_stmt,
        if wild_key.matches(&found_key) && match_key == concrete_key,
        let x = found_key.clone(),
        let y = match_key.clone(),
        let chain = vec![];

    // Find chains for arithmetic operations:
    // 1. Direct value comparisons for sum relationships
    connected_to_target3(result, op1, op2, chain) <--
        target_statement(stmt),
        if let WildcardStatement::SumOf(result_key, operand1_key, operand2_key) = stmt,
        known_int_value(found_result, v1),
        known_int_value(found_op1, v2),
        known_int_value(found_op2, v3),
        if result_key.matches(&found_result),
        if operand1_key == found_op1 && operand2_key == found_op2,
        if let (Value::Int(result_val), Value::Int(op1_val), Value::Int(op2_val)) = (v1, v2, v3),
        if *result_val == *op1_val + *op2_val,
        let result = found_result.clone(),
        let op1 = found_op1.clone(),
        let op2 = found_op2.clone(),
        let chain = vec![(
            NativeOperation::SumOf as u8,
            vec![
                ProvableStatement::ValueOf(result.clone(), v1.clone()),
                ProvableStatement::ValueOf(op1.clone(), v2.clone()),
                ProvableStatement::ValueOf(op2.clone(), v3.clone())
            ],
            ProvableStatement::SumOf(result.clone(), op1.clone(), op2.clone())
        )];

    // 2. Direct value comparisons for product relationships
    connected_to_target3(result, op1, op2, chain) <--
        target_statement(stmt),
        if let WildcardStatement::ProductOf(result_key, operand1_key, operand2_key) = stmt,
        known_int_value(found_result, v1),
        known_int_value(found_op1, v2),
        known_int_value(found_op2, v3),
        if result_key.matches(&found_result),
        if operand1_key == found_op1 && operand2_key == found_op2,
        if let (Value::Int(result_val), Value::Int(op1_val), Value::Int(op2_val)) = (v1, v2, v3),
        if *result_val == *op1_val * *op2_val,
        let result = found_result.clone(),
        let op1 = found_op1.clone(),
        let op2 = found_op2.clone(),
        let chain = vec![(
            NativeOperation::ProductOf as u8,
            vec![
                ProvableStatement::ValueOf(result.clone(), v1.clone()),
                ProvableStatement::ValueOf(op1.clone(), v2.clone()),
                ProvableStatement::ValueOf(op2.clone(), v3.clone())
            ],
            ProvableStatement::ProductOf(result.clone(), op1.clone(), op2.clone())
        )];

    // 3. Direct value comparisons for max relationships
    connected_to_target3(result, op1, op2, chain) <--
        target_statement(stmt),
        if let WildcardStatement::MaxOf(result_key, operand1_key, operand2_key) = stmt,
        known_int_value(found_result, v1),
        known_int_value(found_op1, v2),
        known_int_value(found_op2, v3),
        if result_key.matches(&found_result),
        if operand1_key == found_op1 && operand2_key == found_op2,
        if let (Value::Int(result_val), Value::Int(op1_val), Value::Int(op2_val)) = (v1, v2, v3),
        if *result_val == std::cmp::max(*op1_val, *op2_val),
        let result = found_result.clone(),
        let op1 = found_op1.clone(),
        let op2 = found_op2.clone(),
        let chain = vec![(
            NativeOperation::MaxOf as u8,
            vec![
                ProvableStatement::ValueOf(result.clone(), v1.clone()),
                ProvableStatement::ValueOf(op1.clone(), v2.clone()),
                ProvableStatement::ValueOf(op2.clone(), v3.clone())
            ],
            ProvableStatement::MaxOf(result.clone(), op1.clone(), op2.clone())
        )];
}
