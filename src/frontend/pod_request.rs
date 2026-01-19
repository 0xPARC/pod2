use std::{collections::HashMap, fmt::Display};

use crate::{
    frontend::{Error, Result},
    lang::PrettyPrint,
    middleware::{
        Pod, PredicateOrWildcard, Statement, StatementArg, StatementTmpl, StatementTmplArg, Value,
    },
};

/// Represents a request for a POD, in terms of a set of statement templates.
/// The response should be a POD (or PODs) containing a set of statements which
/// satisfy the templates, with consistent wildcard bindings across all templates.
#[derive(Debug, Clone, PartialEq)]
pub struct PodRequest {
    pub request_templates: Vec<StatementTmpl>,
}

impl PodRequest {
    pub fn new(request_templates: Vec<StatementTmpl>) -> Self {
        Self { request_templates }
    }

    /// Checks if the request is fully satisfied by a single supplied POD.
    /// This checks for exact matches to the statement templates; that is to say
    /// that it performs a "syntactic" match, not a "semantic" match; no
    /// processing of the semantics of the statements is performed.
    pub fn exact_match_pod(&self, pod: &dyn Pod) -> Result<HashMap<String, Value>> {
        let pod_statements = pod.pub_statements();
        let mut bindings: HashMap<String, Value> = HashMap::new();

        if self.dfs_match_all(&pod_statements, &mut bindings, 0) {
            Ok(bindings)
        } else {
            Err(Error::pod_request_validation("No match found".to_string()))
        }
    }

    /// Performs a depth-first search through the statement templates, trying to
    /// match each template to a statement in the POD.
    /// Returns true if all templates are matched, false otherwise.
    /// The bindings map is used to store the bindings of the wildcards to the
    /// values in the POD.
    /// The template_idx is used to track the current template being matched.
    fn dfs_match_all(
        &self,
        pod_statements: &[Statement],
        bindings: &mut HashMap<String, Value>,
        template_idx: usize,
    ) -> bool {
        // Base case: all templates matched
        if template_idx >= self.request_templates.len() {
            return true;
        }

        let template = &self.request_templates[template_idx];

        // Try to match this template with each statement in the POD
        for stmt in pod_statements {
            if let Some(new_bindings) = self.try_match_template(template, stmt, bindings) {
                let original_bindings = bindings.clone();
                bindings.extend(new_bindings);

                if self.dfs_match_all(pod_statements, bindings, template_idx + 1) {
                    return true;
                }

                *bindings = original_bindings;
            }
        }

        false
    }

    fn try_match_template(
        &self,
        template: &StatementTmpl,
        statement: &Statement,
        current_bindings: &HashMap<String, Value>,
    ) -> Option<HashMap<String, Value>> {
        // TODO: Support wildcard
        if template.pred_or_wc != PredicateOrWildcard::Predicate(statement.predicate()) {
            return None;
        }

        let template_args = template.args();
        let statement_args = statement.args();

        if template_args.len() != statement_args.len() {
            return None;
        }

        let mut new_bindings = HashMap::new();

        for (tmpl_arg, stmt_arg) in template_args.iter().zip(statement_args.iter()) {
            if !self.try_match_arg(tmpl_arg, stmt_arg, current_bindings, &mut new_bindings) {
                return None;
            }
        }

        Some(new_bindings)
    }

    fn try_match_arg(
        &self,
        template_arg: &StatementTmplArg,
        statement_arg: &StatementArg,
        current_bindings: &HashMap<String, Value>,
        new_bindings: &mut HashMap<String, Value>,
    ) -> bool {
        match (template_arg, statement_arg) {
            // Literal must match exactly
            (StatementTmplArg::Literal(tmpl_val), StatementArg::Literal(stmt_val)) => {
                tmpl_val == stmt_val
            }

            // Wildcard can bind to any literal value
            (StatementTmplArg::Wildcard(wildcard), StatementArg::Literal(stmt_val)) => self
                .try_bind_wildcard(
                    &wildcard.name,
                    stmt_val.clone(),
                    current_bindings,
                    new_bindings,
                ),

            // AnchoredKey wildcard must match statement's anchored key
            (StatementTmplArg::AnchoredKey(wildcard, tmpl_key), StatementArg::Key(stmt_key)) => {
                // Check if keys match
                if tmpl_key != &stmt_key.key {
                    return false;
                }

                // Try to bind wildcard to the POD ID
                let root_value = Value::from(stmt_key.root);
                self.try_bind_wildcard(&wildcard.name, root_value, current_bindings, new_bindings)
            }

            // Other combinations don't match
            _ => false,
        }
    }

    fn try_bind_wildcard(
        &self,
        wildcard_name: &str,
        value: Value,
        current_bindings: &HashMap<String, Value>,
        new_bindings: &mut HashMap<String, Value>,
    ) -> bool {
        // Check if wildcard is already bound
        if let Some(existing_value) = current_bindings.get(wildcard_name) {
            // Must match existing binding
            return existing_value == &value;
        }

        // Check if we're trying to bind it in new_bindings
        if let Some(existing_value) = new_bindings.get(wildcard_name) {
            // Must match existing binding in this attempt
            return existing_value == &value;
        }

        // Bind the wildcard
        new_bindings.insert(wildcard_name.to_string(), value);
        true
    }

    pub fn templates(&self) -> &[StatementTmpl] {
        &self.request_templates
    }
}

impl Display for PodRequest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_podlang(f)
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        backends::plonky2::{
            mock::mainpod::MockProver, primitives::ec::schnorr::SecretKey, signer::Signer,
        },
        examples::{
            zu_kyc_pod_builder, zu_kyc_pod_request, zu_kyc_sign_dict_builders, MOCK_VD_SET,
        },
        frontend::{MainPodBuilder, Operation},
        lang::parse,
        middleware::{Params, Value},
    };

    #[test]
    fn test_pod_request_exact_match_pod() {
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;

        let (gov_id, pay_stub) = zu_kyc_sign_dict_builders(&params);
        let gov_id = gov_id.sign(&Signer(SecretKey(1u32.into()))).unwrap();
        let pay_stub = pay_stub.sign(&Signer(SecretKey(2u32.into()))).unwrap();
        let builder = zu_kyc_pod_builder(&Params::default(), vd_set, &gov_id, &pay_stub).unwrap();
        let prover = MockProver {};
        let kyc = builder.prove(&prover).unwrap();

        // This request matches the POD
        let request = zu_kyc_pod_request(
            &Value::from(gov_id.public_key),
            &Value::from(pay_stub.public_key),
        )
        .unwrap();
        assert!(request.exact_match_pod(&*kyc.pod).is_ok());

        // This request does not match the POD, because the POD does not contain a NotEqual statement.
        let non_matching_request = parse(
            r#"
        REQUEST(
            NotEqual(4, 5)
        )
        "#,
            &params,
            &[],
        )
        .unwrap()
        .request;
        assert!(non_matching_request.exact_match_pod(&*kyc.pod).is_err());
    }

    #[test]
    fn test_ambiguous_pod() {
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MainPodBuilder::new(&params, vd_set);
        let _sum_of_stmt_1 = builder.pub_op(Operation::sum_of(11, 1, 10));
        let _sum_of_stmt_2 = builder.pub_op(Operation::sum_of(10, 9, 1));
        let _eq_stmt = builder.pub_op(Operation::eq(10, 10));

        let prover = MockProver {};

        let pod = builder.prove(&prover).unwrap();

        println!("{pod}");

        let request = parse(
            r#"
        REQUEST(
            SumOf(a, b, c)
            Equal(a, 10)
        )
        "#,
            &params,
            &[],
        )
        .unwrap();

        let bindings = request.request.exact_match_pod(&*pod.pod).unwrap();
        assert_eq!(*bindings.get("a").unwrap(), 10.into());
        assert_eq!(*bindings.get("b").unwrap(), 9.into());
        assert_eq!(*bindings.get("c").unwrap(), 1.into());
    }
}
