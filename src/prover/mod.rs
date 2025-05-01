pub mod error;
pub mod indexing;
pub mod pod_building;
pub mod solver;
// Keep test_utils public for external integration/library tests if needed
pub mod test_utils;
pub mod translation;
pub mod types;

pub use error::ProverError;

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, sync::Arc};

    use super::*;
    use crate::{
        middleware::{
            self, AnchoredKey, Key, KeyOrWildcard, NativePredicate, Statement, StatementTmpl,
            StatementTmplArg, Value, Wildcard,
        },
        prover::{pod_building, solver, test_utils::*, types::CustomDefinitions},
    };

    #[test]
    fn test_prover_end_to_end_simple_gt() -> Result<(), Box<dyn std::error::Error>> {
        let params = middleware::Params::default();

        // 1. Create mock input SignedPods containing initial key-value data.
        let pod_a =
            create_test_signed_pod(&params, &[("foo", Value::from(10))], "signer_a").unwrap();
        let pod_b =
            create_test_signed_pod(&params, &[("bar", Value::from(20))], "signer_b").unwrap();

        // 2. Define the request template: we want to prove Gt(?y["bar"], ?x["foo"])
        let wc_x = Wildcard::new("x".to_string(), 0); // Wildcard representing pod A's context
        let wc_y = Wildcard::new("y".to_string(), 1); // Wildcard representing pod B's context
        let key_foo = Key::new("foo".to_string());
        let key_bar = Key::new("bar".to_string());

        let request_templates = vec![StatementTmpl {
            pred: middleware::Predicate::Native(NativePredicate::Gt),
            args: vec![
                StatementTmplArg::Key(wc_y.clone(), KeyOrWildcard::Key(key_bar.clone())), // ?y["bar"]
                StatementTmplArg::Key(wc_x.clone(), KeyOrWildcard::Key(key_foo.clone())), // ?x["foo"]
            ],
        }];

        // 3. Prepare inputs for the constraint solver.
        // Index the initial facts (public statements) from the input pods.
        let initial_facts = vec![
            (pod_a.id(), pod_a.get_statement("foo").unwrap()),
            (pod_b.id(), pod_b.get_statement("bar").unwrap()),
        ];
        let indexes = indexing::ProverIndexes::build(params.clone(), &initial_facts);
        let custom_definitions = CustomDefinitions::default();

        // 4. Call the solver to find a consistent assignment and proof steps.
        let solve_result = solver::solve(&request_templates, &indexes, &custom_definitions);
        assert!(
            solve_result.is_ok(),
            "Solver failed: {:?}",
            solve_result.err()
        );
        let solution = solve_result.unwrap();

        // 5. Prepare inputs for the pod building stage.
        let original_signed_pods = HashMap::from([
            (pod_a.id(), Arc::new(pod_a.clone())),
            (pod_b.id(), Arc::new(pod_b.clone())),
        ]);
        let original_main_pods = HashMap::new();

        // 6. Call the pod building process to construct the final MainPod based on the solution.
        let build_result = pod_building::build_main_pod_from_solution(
            &solution,
            &original_signed_pods,
            &original_main_pods,
            &params,
        );
        assert!(
            build_result.is_ok(),
            "Pod building failed: {:?}",
            build_result.err()
        );
        let main_pod = build_result.unwrap();

        // 7. Verify the integrity and correctness of the generated MainPod.
        let verification_result = main_pod.pod.verify();
        assert!(
            verification_result.is_ok(),
            "MainPod verification failed: {:?}",
            verification_result.err()
        );

        // 8. Check that the generated MainPod contains the expected public statements.
        //    In this case, the target Gt statement should be public.
        let expected_public_statement = Statement::Gt(
            AnchoredKey::new(pod_b.id(), key_bar),
            AnchoredKey::new(pod_a.id(), key_foo),
        );
        assert_eq!(
            main_pod.public_statements.len(),
            2,
            "Expected exactly two public statements (Gt and ValueOf for _type)"
        );
        assert!(
            main_pod
                .public_statements
                .contains(&expected_public_statement),
            "Expected Gt statement missing from public statements"
        );

        println!("End-to-end test successful!");
        println!("Generated MainPod: {}", main_pod);

        Ok(())
    }
}
