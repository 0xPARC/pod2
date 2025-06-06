use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use pest::iterators::{Pair, Pairs};
use plonky2::field::types::Field;

use super::error::ProcessorError;
use crate::{
    frontend::{
        BuilderArg, CustomPredicateBatchBuilder, KeyOrWildcardStr, SelfOrWildcardStr,
        StatementTmplBuilder,
    },
    lang::parser::Rule,
    middleware::{
        self, CustomPredicateBatch, CustomPredicateRef, Key, KeyOrWildcard, NativePredicate,
        Params, Predicate, SelfOrWildcard as MiddlewareSelfOrWildcard, StatementTmpl,
        StatementTmplArg, Value, Wildcard, F, VALUE_SIZE,
    },
};

fn get_span(pair: &Pair<Rule>) -> (usize, usize) {
    let span = pair.as_span();
    (span.start(), span.end())
}

pub fn native_predicate_from_string(s: &str) -> Option<NativePredicate> {
    match s {
        "ValueOf" => Some(NativePredicate::ValueOf),
        "Equal" => Some(NativePredicate::Equal),
        "NotEqual" => Some(NativePredicate::NotEqual),
        // Syntactic sugar for Gt/GtEq is handled at a later stage
        "Gt" => Some(NativePredicate::Gt),
        "GtEq" => Some(NativePredicate::GtEq),
        "Lt" => Some(NativePredicate::Lt),
        "LtEq" => Some(NativePredicate::LtEq),
        "Contains" => Some(NativePredicate::Contains),
        "NotContains" => Some(NativePredicate::NotContains),
        "SumOf" => Some(NativePredicate::SumOf),
        "ProductOf" => Some(NativePredicate::ProductOf),
        "MaxOf" => Some(NativePredicate::MaxOf),
        "HashOf" => Some(NativePredicate::HashOf),
        "DictContains" => Some(NativePredicate::DictContains),
        "DictNotContains" => Some(NativePredicate::DictNotContains),
        "ArrayContains" => Some(NativePredicate::ArrayContains),
        "SetContains" => Some(NativePredicate::SetContains),
        "SetNotContains" => Some(NativePredicate::SetNotContains),
        "None" => Some(NativePredicate::None),
        "False" => Some(NativePredicate::False),
        _ => None,
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ProcessedOutput {
    pub custom_batch: Arc<CustomPredicateBatch>,
    pub request_templates: Vec<StatementTmpl>,
}

struct ProcessingContext<'a> {
    params: &'a Params,
    /// Maps predicate names to their batch index and public argument count (from Pass 1)
    custom_predicate_signatures: HashMap<String, (usize, usize)>,
    /// Stores the original Pest pairs for custom predicate definitions for Pass 2
    custom_predicate_pairs: Vec<Pair<'a, Rule>>,
    /// Stores the original Pest pair for the request definition for Pass 2
    request_pair: Option<Pair<'a, Rule>>,
}

impl<'a> ProcessingContext<'a> {
    fn new(params: &'a Params) -> Self {
        ProcessingContext {
            params,
            custom_predicate_signatures: HashMap::new(),
            custom_predicate_pairs: Vec::new(),
            request_pair: None,
        }
    }
}

pub fn process_pest_tree(
    mut pairs_iterator_for_document_rule: Pairs<'_, Rule>,
    params: &Params,
) -> Result<ProcessedOutput, ProcessorError> {
    let mut processing_ctx = ProcessingContext::new(params);

    let document_node = pairs_iterator_for_document_rule.next().ok_or_else(|| {
        ProcessorError::Internal(format!(
            "Parser returned no pairs for the expected top-level rule: {:?}.",
            Rule::document
        ))
    })?;

    if document_node.as_rule() != Rule::document {
        return Err(ProcessorError::Internal(format!(
            "Expected top-level pair to be Rule::{:?}, but found Rule::{:?}.",
            Rule::document,
            document_node.as_rule()
        )));
    }

    let document_content_pairs = document_node.into_inner();

    first_pass(document_content_pairs, &mut processing_ctx)?;

    second_pass(&mut processing_ctx)
}

/// Pass 1: Iterates through top-level definitions, records custom predicate
/// signatures and stores pairs for Pass 2.
fn first_pass<'a>(
    document_pairs: Pairs<'a, Rule>,
    ctx: &mut ProcessingContext<'a>,
) -> Result<(), ProcessorError> {
    let mut defined_custom_names: HashSet<String> = HashSet::new();
    let mut first_request_span: Option<(usize, usize)> = None;

    for pair in document_pairs {
        match pair.as_rule() {
            Rule::custom_predicate_def => {
                let pred_name_pair = pair
                    .clone()
                    .into_inner()
                    .find(|p| p.as_rule() == Rule::identifier)
                    .ok_or_else(|| ProcessorError::MissingElement {
                        element_type: "predicate name".to_string(),
                        context: "custom_predicate_def".to_string(),
                        span: Some(get_span(&pair)),
                    })?;
                let pred_name = pred_name_pair.as_str().to_string();

                if defined_custom_names.contains(&pred_name) {
                    return Err(ProcessorError::DuplicateDefinition {
                        name: pred_name,
                        span: Some(get_span(&pred_name_pair)),
                    });
                }
                defined_custom_names.insert(pred_name.clone());

                let public_arity = count_public_args(&pair)?;
                ctx.custom_predicate_signatures.insert(
                    pred_name.clone(),
                    (ctx.custom_predicate_pairs.len(), public_arity),
                );
                ctx.custom_predicate_pairs.push(pair);
            }
            Rule::request_def => {
                if ctx.request_pair.is_some() {
                    return Err(ProcessorError::MultipleRequestDefinitions {
                        first_span: first_request_span,
                        second_span: Some(get_span(&pair)),
                    });
                }
                first_request_span = Some(get_span(&pair));
                ctx.request_pair = Some(pair);
            }
            Rule::EOI => break,
            Rule::COMMENT | Rule::WHITESPACE => {}
            _ => {
                return Err(ProcessorError::RuleMismatch {
                    expected_rule: Rule::custom_predicate_def,
                    found_rule: pair.as_rule(),
                    context: "top-level document content (expected custom_predicate_def, request_def, or EOI)".to_string(),
                    span: Some(get_span(&pair)),
                });
            }
        }
    }
    Ok(())
}

fn count_public_args(pred_def_pair: &Pair<Rule>) -> Result<usize, ProcessorError> {
    let arg_section_pair = pred_def_pair
        .clone()
        .into_inner()
        .find(|p| p.as_rule() == Rule::arg_section)
        .ok_or_else(|| ProcessorError::MissingElement {
            element_type: "arg_section".to_string(),
            context: "custom_predicate_def (count_public_args)".to_string(),
            span: Some(get_span(pred_def_pair)),
        })?;

    let arg_section_span = get_span(&arg_section_pair);

    let public_arg_list_pair = arg_section_pair
        .into_inner()
        .find(|p| p.as_rule() == Rule::public_arg_list)
        .ok_or_else(|| ProcessorError::MissingElement {
            element_type: "public_arg_list".to_string(),
            context: "arg_section in custom_predicate_def (count_public_args)".to_string(),
            span: Some(arg_section_span),
        })?;

    Ok(public_arg_list_pair
        .into_inner()
        .filter(|p| p.as_rule() == Rule::identifier)
        .count())
}

fn second_pass(ctx: &mut ProcessingContext) -> Result<ProcessedOutput, ProcessorError> {
    let mut cpb_builder =
        CustomPredicateBatchBuilder::new(ctx.params.clone(), "PodlogBatch".to_string());

    for pred_pair in &ctx.custom_predicate_pairs {
        process_and_add_custom_predicate_to_batch(pred_pair, ctx, &mut cpb_builder)?;
    }

    let custom_batch = cpb_builder.finish();

    if custom_batch.predicates.len() > ctx.params.max_custom_batch_size {
        return Err(ProcessorError::Middleware(middleware::Error::max_length(
            "custom predicates".to_string(),
            custom_batch.predicates.len(),
            ctx.params.max_custom_batch_size,
        )));
    }

    let request_templates = if let Some(req_pair) = &ctx.request_pair {
        process_request_def(req_pair, ctx, &custom_batch)?
    } else {
        Vec::new()
    };

    Ok(ProcessedOutput {
        custom_batch,
        request_templates,
    })
}

fn pest_pair_to_builder_arg(
    arg_content_pair: &Pair<Rule>,
    context_stmt_name: &str,
) -> Result<BuilderArg, ProcessorError> {
    match arg_content_pair.as_rule() {
        Rule::literal_value => {
            let value = process_literal_value(arg_content_pair, context_stmt_name)?;
            Ok(BuilderArg::Literal(value))
        }
        Rule::wildcard => {
            let full_name = arg_content_pair.as_str();
            let name_only =
                full_name
                    .strip_prefix("?")
                    .ok_or_else(|| ProcessorError::Semantic {
                        message: format!("Invalid wildcard format for BuilderArg: {}", full_name),
                        span: Some(get_span(arg_content_pair)),
                    })?;
            if name_only.is_empty() {
                return Err(ProcessorError::Semantic {
                    message: "Wildcard name cannot be empty after '?' for BuilderArg".to_string(),
                    span: Some(get_span(arg_content_pair)),
                });
            }
            Ok(BuilderArg::WildcardLiteral(name_only.to_string()))
        }
        Rule::anchored_key => {
            let mut inner_ak_pairs = arg_content_pair.clone().into_inner();
            let pod_id_pair =
                inner_ak_pairs
                    .next()
                    .ok_or_else(|| ProcessorError::MissingElement {
                        element_type: "pod identifier (SELF or ?Var) for BuilderArg".to_string(),
                        context: format!("anchored key in {}", context_stmt_name),
                        span: Some(get_span(arg_content_pair)),
                    })?;

            let pod_self_or_wc_str = match pod_id_pair.as_rule() {
                Rule::wildcard => {
                    let name = pod_id_pair.as_str().strip_prefix("?").unwrap_or_default();
                    if name.is_empty() {
                        return Err(ProcessorError::Semantic {
                            message: "Wildcard name for pod_id cannot be empty after '?'"
                                .to_string(),
                            span: Some(get_span(&pod_id_pair)),
                        });
                    }
                    SelfOrWildcardStr::Wildcard(name.to_string())
                }
                Rule::self_keyword => SelfOrWildcardStr::SELF,
                _ => {
                    return Err(ProcessorError::RuleMismatch {
                        expected_rule: Rule::wildcard, // Or Rule::self_keyword
                        found_rule: pod_id_pair.as_rule(),
                        context: format!(
                            "pod identifier part of anchored key in {} for BuilderArg",
                            context_stmt_name
                        ),
                        span: Some(get_span(&pod_id_pair)),
                    });
                }
            };

            let key_part_pair = inner_ak_pairs.next().ok_or_else(|| {
                println!("inner_ak_pairs: {:?}", inner_ak_pairs.clone());
                ProcessorError::MissingElement {
                    element_type: "key part ([?KeyVar] or [\"key_str\"]) for BuilderArg"
                        .to_string(),
                    context: format!(
                        "anchored key {} in {}",
                        pod_id_pair.as_str(),
                        context_stmt_name
                    ),
                    span: Some(get_span(arg_content_pair)),
                }
            })?;

            let key_or_wildcard_str = match key_part_pair.as_rule() {
                Rule::wildcard => {
                    let key_wildcard_name =
                        key_part_pair.as_str().strip_prefix("?").unwrap_or_default();
                    if key_wildcard_name.is_empty() {
                        return Err(ProcessorError::Semantic {
                            message: "Wildcard name for key_part cannot be empty after '?'"
                                .to_string(),
                            span: Some(get_span(&key_part_pair)),
                        });
                    }
                    KeyOrWildcardStr::Wildcard(key_wildcard_name.to_string())
                }
                Rule::literal_string => {
                    let key_str_literal = parse_pest_string_literal(&key_part_pair)?;
                    KeyOrWildcardStr::Key(key_str_literal)
                }
                _ => {
                    return Err(ProcessorError::RuleMismatch {
                        expected_rule: Rule::wildcard,
                        found_rule: key_part_pair.as_rule(),
                        context: format!(
                            "key part of anchored key {} in {} for BuilderArg",
                            pod_id_pair.as_str(),
                            context_stmt_name
                        ),
                        span: Some(get_span(&key_part_pair)),
                    });
                }
            };
            Ok(BuilderArg::Key(pod_self_or_wc_str, key_or_wildcard_str))
        }
        _ => Err(ProcessorError::RuleMismatch {
            expected_rule: Rule::statement_arg,
            found_rule: arg_content_pair.as_rule(),
            context: format!("argument parsing for BuilderArg in {}", context_stmt_name),
            span: Some(get_span(arg_content_pair)),
        }),
    }
}

fn validate_and_build_statement_template(
    stmt_name_str: &str,
    pred: &Predicate,
    args: Vec<BuilderArg>,
    processing_ctx: &ProcessingContext,
    stmt_span: (usize, usize),
    stmt_name_span: (usize, usize),
) -> Result<StatementTmplBuilder, ProcessorError> {
    match pred {
        Predicate::Native(native_pred) => {
            let (expected_arity, mapped_pred_for_arity_check) = match native_pred {
                NativePredicate::Gt => (2, NativePredicate::Lt),
                NativePredicate::GtEq => (2, NativePredicate::LtEq),
                NativePredicate::ValueOf
                | NativePredicate::Equal
                | NativePredicate::NotEqual
                | NativePredicate::Lt
                | NativePredicate::LtEq
                | NativePredicate::SetContains
                | NativePredicate::DictNotContains
                | NativePredicate::SetNotContains => (2, *native_pred),
                NativePredicate::NotContains
                | NativePredicate::Contains
                | NativePredicate::ArrayContains
                | NativePredicate::DictContains
                | NativePredicate::SumOf
                | NativePredicate::ProductOf
                | NativePredicate::MaxOf
                | NativePredicate::HashOf => (3, *native_pred),
                NativePredicate::None | NativePredicate::False => (0, *native_pred),
            };

            if args.len() != expected_arity {
                return Err(ProcessorError::ArgumentCountMismatch {
                    predicate: stmt_name_str.to_string(),
                    expected: expected_arity,
                    found: args.len(),
                    span: Some(stmt_name_span),
                });
            }

            if mapped_pred_for_arity_check == NativePredicate::ValueOf {
                if !matches!(args.get(0), Some(BuilderArg::Key(..))) {
                    return Err(ProcessorError::TypeError {
                        expected: "Anchored Key".to_string(),
                        found: args
                            .get(0)
                            .map_or("None".to_string(), |a| format!("{:?}", a)),
                        item: format!("argument 1 of native predicate '{}'", stmt_name_str),
                        span: Some(stmt_span),
                    });
                }
                if !matches!(args.get(1), Some(BuilderArg::Literal(..))) {
                    return Err(ProcessorError::TypeError {
                        expected: "Literal".to_string(),
                        found: args
                            .get(1)
                            .map_or("None".to_string(), |a| format!("{:?}", a)),
                        item: format!("argument 2 of native predicate '{}'", stmt_name_str),
                        span: Some(stmt_span),
                    });
                }
            } else if expected_arity > 0 {
                for (i, arg) in args.iter().enumerate() {
                    if !matches!(arg, BuilderArg::Key(..)) {
                        return Err(ProcessorError::TypeError {
                            expected: "Anchored Key".to_string(),
                            found: format!("{:?}", arg),
                            item: format!(
                                "argument {} of native predicate '{}'",
                                i + 1,
                                stmt_name_str
                            ),
                            span: Some(stmt_span),
                        });
                    }
                }
            }
        }
        Predicate::Custom(_) | Predicate::BatchSelf(_) => {
            let (_original_pred_idx, expected_arity_val) = processing_ctx
                .custom_predicate_signatures
                .get(stmt_name_str)
                .ok_or_else(|| {
                    ProcessorError::Internal(format!(
                        "Custom predicate signature not found for '{}' during validation",
                        stmt_name_str
                    ))
                })?;

            if args.len() != *expected_arity_val {
                return Err(ProcessorError::ArgumentCountMismatch {
                    predicate: stmt_name_str.to_string(),
                    expected: *expected_arity_val,
                    found: args.len(),
                    span: Some(stmt_name_span),
                });
            }

            for (idx, arg) in args.iter().enumerate() {
                if !matches!(arg, BuilderArg::WildcardLiteral(_) | BuilderArg::Literal(_)) {
                    return Err(ProcessorError::TypeError {
                        expected: "Wildcard or Literal".to_string(),
                        found: format!("{:?}", arg),
                        item: format!(
                            "argument {} of custom predicate call '{}'",
                            idx + 1,
                            stmt_name_str
                        ),
                        span: Some(stmt_span),
                    });
                }
            }
        }
    }

    let mut stb = StatementTmplBuilder::new(pred.clone());
    for arg in args {
        stb = stb.arg(arg);
    }
    Ok(stb.desugar())
}

fn process_and_add_custom_predicate_to_batch(
    pred_def_pair: &Pair<Rule>,
    processing_ctx: &ProcessingContext,
    cpb_builder: &mut CustomPredicateBatchBuilder,
) -> Result<(), ProcessorError> {
    let mut inner_pairs = pred_def_pair.clone().into_inner();
    let name_pair = inner_pairs
        .find(|p| p.as_rule() == Rule::identifier)
        .ok_or_else(|| ProcessorError::MissingElement {
            element_type: "predicate name".to_string(),
            context: "custom_predicate_def".to_string(),
            span: Some(get_span(pred_def_pair)),
        })?;
    let name = name_pair.as_str().to_string();

    let arg_section_pair = inner_pairs
        .find(|p| p.as_rule() == Rule::arg_section)
        .ok_or_else(|| ProcessorError::MissingElement {
            element_type: "arg_section".to_string(),
            context: "custom_predicate_def".to_string(),
            span: Some(get_span(pred_def_pair)),
        })?;

    let mut public_arg_strings: Vec<String> = Vec::new();
    let mut private_arg_strings: Vec<String> = Vec::new();
    let mut defined_arg_names: HashSet<String> = HashSet::new();

    for arg_part_pair in arg_section_pair.into_inner() {
        match arg_part_pair.as_rule() {
            Rule::public_arg_list => {
                for arg_ident_pair in arg_part_pair
                    .into_inner()
                    .filter(|p| p.as_rule() == Rule::identifier)
                {
                    let arg_name = arg_ident_pair.as_str().to_string();
                    if !defined_arg_names.insert(arg_name.clone()) {
                        return Err(ProcessorError::DuplicateWildcard {
                            name: arg_name,
                            span: Some(get_span(&arg_ident_pair)),
                        });
                    }
                    public_arg_strings.push(arg_name);
                }
            }
            Rule::private_arg_list => {
                for arg_ident_pair in arg_part_pair
                    .into_inner()
                    .filter(|p| p.as_rule() == Rule::identifier)
                {
                    let arg_name = arg_ident_pair.as_str().to_string();
                    if !defined_arg_names.insert(arg_name.clone()) {
                        return Err(ProcessorError::DuplicateWildcard {
                            name: arg_name,
                            span: Some(get_span(&arg_ident_pair)),
                        });
                    }
                    private_arg_strings.push(arg_name);
                }
            }
            Rule::private_kw | Rule::COMMENT | Rule::WHITESPACE => {}
            _ if arg_part_pair.as_str() == "," => {}
            _ => {
                return Err(ProcessorError::RuleMismatch {
                    expected_rule: Rule::public_arg_list,
                    found_rule: arg_part_pair.as_rule(),
                    context: format!("arguments for predicate {}", name),
                    span: Some(get_span(&arg_part_pair)),
                });
            }
        }
    }

    let conjunction_type_pair = inner_pairs
        .find(|p| p.as_rule() == Rule::conjunction_type)
        .ok_or_else(|| ProcessorError::MissingElement {
            element_type: "conjunction type (AND/OR)".to_string(),
            context: format!("definition of predicate {}", name),
            span: Some(get_span(pred_def_pair)),
        })?;
    let conjunction = match conjunction_type_pair.as_str() {
        "AND" => true,
        "OR" => false,
        _ => {
            return Err(ProcessorError::Semantic {
                message: format!(
                    "Invalid conjunction type: {}",
                    conjunction_type_pair.as_str()
                ),
                span: Some(get_span(&conjunction_type_pair)),
            })
        }
    };

    let statement_list_pair = inner_pairs
        .find(|p| p.as_rule() == Rule::statement_list)
        .ok_or_else(|| ProcessorError::MissingElement {
            element_type: "statement list".to_string(),
            context: format!("definition of predicate {}", name),
            span: Some(get_span(pred_def_pair)),
        })?;

    let mut statement_builders = Vec::new();
    for stmt_pair in statement_list_pair
        .into_inner()
        .filter(|p| p.as_rule() == Rule::statement)
    {
        let mut inner_stmt_pairs = stmt_pair.clone().into_inner();
        let stmt_name_pair = inner_stmt_pairs
            .find(|p| p.as_rule() == Rule::identifier)
            .ok_or_else(|| ProcessorError::MissingElement {
                element_type: "statement name".to_string(),
                context: "statement parsing".to_string(),
                span: Some(get_span(&stmt_pair)),
            })?;
        let stmt_name_str = stmt_name_pair.as_str();

        let builder_args = parse_statement_args(&stmt_pair, stmt_name_str)?;

        let middleware_predicate_type =
            if let Some(native_pred) = native_predicate_from_string(stmt_name_str) {
                Predicate::Native(native_pred)
            } else if let Some((pred_index, _expected_arity)) = processing_ctx
                .custom_predicate_signatures
                .get(stmt_name_str)
            {
                Predicate::BatchSelf(*pred_index)
            } else {
                return Err(ProcessorError::UndefinedIdentifier {
                    name: stmt_name_str.to_string(),
                    span: Some(get_span(&stmt_name_pair)),
                });
            };

        let stb = validate_and_build_statement_template(
            stmt_name_str,
            &middleware_predicate_type,
            builder_args, // Consumed
            processing_ctx,
            get_span(&stmt_pair),
            get_span(&stmt_name_pair),
        )?;
        statement_builders.push(stb);
    }

    let public_args_strs: Vec<&str> = public_arg_strings.iter().map(AsRef::as_ref).collect();
    let private_args_strs: Vec<&str> = private_arg_strings.iter().map(AsRef::as_ref).collect();
    let sts_slice: &[StatementTmplBuilder] = &statement_builders;

    if conjunction {
        cpb_builder.predicate_and(&name, &public_args_strs, &private_args_strs, sts_slice)?;
    } else {
        cpb_builder.predicate_or(&name, &public_args_strs, &private_args_strs, sts_slice)?;
    }

    Ok(())
}

fn process_request_def(
    req_def_pair: &Pair<Rule>,
    processing_ctx: &ProcessingContext,
    custom_batch: &Arc<CustomPredicateBatch>,
) -> Result<Vec<StatementTmpl>, ProcessorError> {
    let mut request_wildcard_names: Vec<String> = Vec::new();
    let mut defined_request_wildcards: HashSet<String> = HashSet::new();

    let mut request_statement_builders: Vec<StatementTmplBuilder> = Vec::new();

    if let Some(statement_list_pair) = req_def_pair
        .clone()
        .into_inner()
        .find(|p| p.as_rule() == Rule::statement_list)
    {
        for stmt_pair in statement_list_pair
            .into_inner()
            .filter(|p| p.as_rule() == Rule::statement)
        {
            let built_stb = process_proof_request_statement_template(
                &stmt_pair,
                processing_ctx,
                Some(custom_batch), // Pass as Option<&Arc<...>>
                &mut request_wildcard_names,
                &mut defined_request_wildcards,
            )?;
            request_statement_builders.push(built_stb);
        }
    }

    let mut request_templates: Vec<StatementTmpl> =
        Vec::with_capacity(request_statement_builders.len());
    for stb in request_statement_builders {
        let tmpl =
            resolve_request_statement_builder(stb, &request_wildcard_names, processing_ctx.params)?;
        request_templates.push(tmpl);
    }

    if request_templates.len() > processing_ctx.params.max_statements {
        return Err(ProcessorError::Middleware(middleware::Error::max_length(
            "request statements".to_string(),
            request_templates.len(),
            processing_ctx.params.max_statements,
        )));
    }
    Ok(request_templates)
}

fn process_proof_request_statement_template(
    stmt_pair: &Pair<Rule>,
    processing_ctx: &ProcessingContext,
    custom_batch_for_request: Option<&Arc<CustomPredicateBatch>>,
    request_wildcard_names: &mut Vec<String>,
    defined_request_wildcards: &mut HashSet<String>,
) -> Result<StatementTmplBuilder, ProcessorError> {
    let mut inner_stmt_pairs = stmt_pair.clone().into_inner();
    let name_pair = inner_stmt_pairs
        .find(|p| p.as_rule() == Rule::identifier)
        .ok_or_else(|| ProcessorError::MissingElement {
            element_type: "statement name".to_string(),
            context: "statement parsing".to_string(),
            span: Some(get_span(stmt_pair)),
        })?;
    let stmt_name_str = name_pair.as_str();

    let builder_args = parse_statement_args(stmt_pair, stmt_name_str)?;
    let mut temp_stmt_wildcard_names: Vec<String> = Vec::new();

    for arg in &builder_args {
        match arg {
            BuilderArg::WildcardLiteral(name) => temp_stmt_wildcard_names.push(name.clone()),
            BuilderArg::Key(pod_id_str, key_wc_str) => {
                if let SelfOrWildcardStr::Wildcard(name) = pod_id_str {
                    temp_stmt_wildcard_names.push(name.clone());
                }
                if let KeyOrWildcardStr::Wildcard(key_wc_name) = key_wc_str {
                    temp_stmt_wildcard_names.push(key_wc_name.clone());
                }
            }
            _ => {}
        }
    }

    for name in temp_stmt_wildcard_names {
        if defined_request_wildcards.insert(name.clone()) {
            request_wildcard_names.push(name);
        }
    }

    let middleware_predicate_type =
        if let Some(native_pred) = native_predicate_from_string(stmt_name_str) {
            Predicate::Native(native_pred)
        } else if let Some((pred_index, _expected_arity)) = processing_ctx
            .custom_predicate_signatures
            .get(stmt_name_str)
        {
            if let Some(batch_ref) = custom_batch_for_request {
                Predicate::Custom(CustomPredicateRef::new(batch_ref.clone(), *pred_index))
            } else {
                return Err(ProcessorError::Internal(format!(
                "Custom predicate '{}' found but no custom batch provided for request processing.",
                stmt_name_str
            )));
            }
        } else {
            return Err(ProcessorError::UndefinedIdentifier {
                name: stmt_name_str.to_string(),
                span: Some(get_span(&name_pair)),
            });
        };

    let stb = validate_and_build_statement_template(
        stmt_name_str,
        &middleware_predicate_type,
        builder_args,
        processing_ctx,
        get_span(stmt_pair),
        get_span(&name_pair),
    )?;

    Ok(stb.desugar())
}

fn process_literal_value(
    lit_val_pair: &Pair<Rule>,
    context_stmt_name: &str,
) -> Result<Value, ProcessorError> {
    let inner_lit =
        lit_val_pair
            .clone()
            .into_inner()
            .next()
            .ok_or_else(|| ProcessorError::MissingElement {
                element_type: "literal content".to_string(),
                context: format!("literal in {}", context_stmt_name),
                span: Some(get_span(lit_val_pair)),
            })?;

    match inner_lit.as_rule() {
        Rule::literal_int => {
            let val = inner_lit.as_str().parse::<i64>().map_err(|_e| {
                ProcessorError::InvalidLiteralFormat {
                    kind: "int".to_string(),
                    value: inner_lit.as_str().to_string(),
                    span: Some(get_span(&inner_lit)),
                }
            })?;
            Ok(Value::from(val))
        }
        Rule::literal_bool => {
            let val = inner_lit.as_str().parse::<bool>().map_err(|_e| {
                ProcessorError::InvalidLiteralFormat {
                    kind: "bool".to_string(),
                    value: inner_lit.as_str().to_string(),
                    span: Some(get_span(&inner_lit)),
                }
            })?;
            Ok(Value::from(val))
        }
        Rule::literal_raw => {
            let full_literal_str = inner_lit.as_str();
            let hex_str_no_prefix = full_literal_str
                .strip_prefix("0x")
                .unwrap_or(full_literal_str);

            parse_hex_str_to_raw_value(hex_str_no_prefix)
                .map_err(|e| match e {
                    ProcessorError::InvalidLiteralFormat { kind, value, .. } => {
                        ProcessorError::InvalidLiteralFormat {
                            kind,
                            value,
                            span: Some(get_span(&inner_lit)),
                        }
                    }
                    ProcessorError::Internal(message) => ProcessorError::InvalidLiteralFormat {
                        kind: format!("raw hex processing (internal: {})", message),
                        value: full_literal_str.to_string(),
                        span: Some(get_span(&inner_lit)),
                    },
                    _ => ProcessorError::InvalidLiteralFormat {
                        kind: "raw hex processing error".to_string(),
                        value: full_literal_str.to_string(),
                        span: Some(get_span(&inner_lit)),
                    },
                })
                .map(Value::from)
        }
        Rule::literal_string => Ok(Value::from(parse_pest_string_literal(&inner_lit)?)),
        Rule::literal_array => {
            let elements: Result<Vec<Value>, ProcessorError> = inner_lit
                .into_inner()
                .map(|elem_pair| process_literal_value(&elem_pair, context_stmt_name))
                .collect();
            let middleware_array = middleware::containers::Array::new(elements?)
                .map_err(|e| ProcessorError::Internal(format!("Failed to create Array: {}", e)))?;
            Ok(Value::from(middleware_array))
        }
        Rule::literal_set => {
            let elements: Result<HashSet<Value>, ProcessorError> = inner_lit
                .into_inner()
                .map(|elem_pair| process_literal_value(&elem_pair, context_stmt_name))
                .collect();
            let middleware_set = middleware::containers::Set::new(elements?)
                .map_err(|e| ProcessorError::Internal(format!("Failed to create Set: {}", e)))?;
            Ok(Value::from(middleware_set))
        }
        Rule::literal_dict => {
            let pairs: Result<HashMap<Key, Value>, ProcessorError> = inner_lit
                .into_inner()
                .map(|dict_entry_pair| {
                    let mut entry_inner = dict_entry_pair.clone().into_inner();
                    let key_pair =
                        entry_inner
                            .next()
                            .ok_or_else(|| ProcessorError::MissingElement {
                                element_type: "dict key".to_string(),
                                context: format!("dict in {}", context_stmt_name),
                                span: Some(get_span(&dict_entry_pair)),
                            })?;
                    let val_pair =
                        entry_inner
                            .next()
                            .ok_or_else(|| ProcessorError::MissingElement {
                                element_type: "dict value".to_string(),
                                context: format!("dict in {}", context_stmt_name),
                                span: Some(get_span(&dict_entry_pair)),
                            })?;
                    let key_str = parse_pest_string_literal(&key_pair)?;
                    let val = process_literal_value(&val_pair, context_stmt_name)?;
                    Ok((Key::new(key_str), val))
                })
                .collect();
            let middleware_dict = middleware::containers::Dictionary::new(pairs?).map_err(|e| {
                ProcessorError::Internal(format!("Failed to create Dictionary: {}", e))
            })?;
            Ok(Value::from(middleware_dict))
        }
        _ => Err(ProcessorError::RuleMismatch {
            expected_rule: Rule::literal_value,
            found_rule: inner_lit.as_rule(),
            context: format!("literal parsing for {}", context_stmt_name),
            span: Some(get_span(&inner_lit)),
        }),
    }
}

fn parse_pest_string_literal(pair: &Pair<Rule>) -> Result<String, ProcessorError> {
    if pair.as_rule() != Rule::literal_string && pair.as_rule() != Rule::inner {
        let actual_rule = if pair.as_rule() == Rule::literal_string {
            pair.clone().into_inner().next().map(|p| p.as_rule())
        } else {
            Some(pair.as_rule())
        };

        if actual_rule != Some(Rule::inner) {
            return Err(ProcessorError::RuleMismatch {
                expected_rule: Rule::literal_string,
                found_rule: pair.as_rule(),
                context: "string literal parsing".to_string(),
                span: Some(get_span(pair)),
            });
        }
    }

    let inner_pair = if pair.as_rule() == Rule::literal_string {
        pair.clone()
            .into_inner()
            .next()
            .ok_or_else(|| ProcessorError::MissingElement {
                element_type: "string content".to_string(),
                context: "string literal".to_string(),
                span: Some(get_span(pair)),
            })?
    } else {
        pair.clone()
    };

    let raw_content = inner_pair.as_str();
    let mut result = String::with_capacity(raw_content.len());
    let mut chars = raw_content.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('"') => result.push('"'),
                Some('\\') => result.push('\\'),
                Some('/') => result.push('/'),
                Some('b') => result.push('\x08'),
                Some('f') => result.push('\x0C'),
                Some('n') => result.push('\n'),
                Some('r') => result.push('\r'),
                Some('t') => result.push('\t'),
                Some('u') => {
                    let mut hex_code = String::with_capacity(4);
                    for _ in 0..4 {
                        hex_code.push(chars.next().ok_or_else(|| {
                            ProcessorError::InvalidLiteralFormat {
                                kind: "unicode escape".to_string(),
                                value: format!("\\u{}... (incomplete)", hex_code),
                                span: Some(get_span(&inner_pair)),
                            }
                        })?);
                    }
                    let char_code = u32::from_str_radix(&hex_code, 16).map_err(|_| {
                        ProcessorError::InvalidLiteralFormat {
                            kind: "unicode escape".to_string(),
                            value: format!("\\u{}", hex_code),
                            span: Some(get_span(&inner_pair)),
                        }
                    })?;
                    result.push(std::char::from_u32(char_code).ok_or_else(|| {
                        ProcessorError::InvalidLiteralFormat {
                            kind: "unicode escape (invalid code point)".to_string(),
                            value: format!("\\u{}", hex_code),
                            span: Some(get_span(&inner_pair)),
                        }
                    })?);
                }
                Some(other) => {
                    return Err(ProcessorError::InvalidLiteralFormat {
                        kind: "escape sequence".to_string(),
                        value: format!("\\{}", other),
                        span: Some(get_span(&inner_pair)),
                    })
                }
                None => {
                    return Err(ProcessorError::InvalidLiteralFormat {
                        kind: "escape sequence".to_string(),
                        value: "\\ (ends with escape)".to_string(),
                        span: Some(get_span(&inner_pair)),
                    })
                }
            }
        } else {
            result.push(c);
        }
    }
    Ok(result)
}

fn parse_hex_str_to_raw_value(hex_str: &str) -> Result<middleware::RawValue, ProcessorError> {
    const EXPECTED_HEX_CHARS_PER_FELT: usize = 16; // Each F element is a u64, requiring 16 hex characters
    const EXPECTED_TOTAL_HEX_CHARS: usize = VALUE_SIZE * EXPECTED_HEX_CHARS_PER_FELT;

    if hex_str.len() != EXPECTED_TOTAL_HEX_CHARS {
        return Err(ProcessorError::Internal(format!(
            "Internal error: Expected {} hex characters for RawValue ({} F elements * {} hex/F), got {}.",
            EXPECTED_TOTAL_HEX_CHARS,
            VALUE_SIZE,
            EXPECTED_HEX_CHARS_PER_FELT,
            hex_str.len()
        )));
    }

    let mut v = [F::ZERO; VALUE_SIZE];
    let value_range = 0..VALUE_SIZE;
    for i in value_range {
        let start_idx = i * EXPECTED_HEX_CHARS_PER_FELT;
        let end_idx = start_idx + EXPECTED_HEX_CHARS_PER_FELT;
        let hex_part = &hex_str[start_idx..end_idx];

        let u64_val = u64::from_str_radix(hex_part, 16).map_err(|e| {
            ProcessorError::InvalidLiteralFormat {
                kind: format!("raw hex (parse error for segment '{}')", hex_part),
                value: e.to_string(),
                span: None,
            }
        })?;
        v[i] = F::from_canonical_u64(u64_val);
    }
    Ok(middleware::RawValue(v))
}

// Helper to resolve a wildcard name string to an indexed middleware::Wildcard
// based on an ordered list of names from the current scope (e.g., request or predicate def).
fn resolve_wildcard(
    ordered_scope_wildcard_names: &[String],
    name_to_resolve: &str,
) -> Result<Wildcard, ProcessorError> {
    ordered_scope_wildcard_names
        .iter()
        .position(|n| n == name_to_resolve)
        .map(|index| Wildcard::new(name_to_resolve.to_string(), index))
        .ok_or_else(|| ProcessorError::UndefinedWildcard {
            name: name_to_resolve.to_string(),
            span: None,
        })
}

fn resolve_key_or_wildcard_str(
    ordered_scope_wildcard_names: &[String],
    kows: &KeyOrWildcardStr,
) -> Result<KeyOrWildcard, ProcessorError> {
    match kows {
        KeyOrWildcardStr::Key(k_str) => Ok(KeyOrWildcard::Key(Key::new(k_str.clone()))),
        KeyOrWildcardStr::Wildcard(wc_name_str) => {
            let resolved_wc = resolve_wildcard(ordered_scope_wildcard_names, wc_name_str)?;
            Ok(KeyOrWildcard::Wildcard(resolved_wc))
        }
    }
}

fn resolve_request_statement_builder(
    stb: StatementTmplBuilder,
    ordered_request_wildcard_names: &[String],
    params: &Params,
) -> Result<StatementTmpl, ProcessorError> {
    let stb = stb.desugar();

    let mut middleware_args = Vec::with_capacity(stb.args.len());
    for builder_arg in stb.args {
        let mw_arg = match builder_arg {
            BuilderArg::Literal(v) => StatementTmplArg::Literal(v),
            BuilderArg::Key(pod_id_str, key_wc_str) => {
                let pod_sowc = match pod_id_str {
                    SelfOrWildcardStr::SELF => MiddlewareSelfOrWildcard::SELF,
                    SelfOrWildcardStr::Wildcard(name) => MiddlewareSelfOrWildcard::Wildcard(
                        resolve_wildcard(ordered_request_wildcard_names, &name)?,
                    ),
                };
                let key_or_wc =
                    resolve_key_or_wildcard_str(ordered_request_wildcard_names, &key_wc_str)?;
                StatementTmplArg::AnchoredKey(pod_sowc, key_or_wc)
            }
            BuilderArg::WildcardLiteral(wc_name) => {
                let pod_wc = resolve_wildcard(ordered_request_wildcard_names, &wc_name)?;
                StatementTmplArg::WildcardLiteral(pod_wc)
            }
        };
        middleware_args.push(mw_arg);
    }

    if middleware_args.len() > params.max_statement_args {
        return Err(ProcessorError::Middleware(middleware::Error::max_length(
            format!("Arguments for predicate {:?}", stb.predicate),
            middleware_args.len(),
            params.max_statement_args,
        )));
    }

    Ok(StatementTmpl {
        pred: stb.predicate,
        args: middleware_args,
    })
}

fn parse_statement_args(
    stmt_pair: &Pair<Rule>,
    context_stmt_name: &str,
) -> Result<Vec<BuilderArg>, ProcessorError> {
    let mut builder_args = Vec::new();
    let mut inner_stmt_pairs = stmt_pair.clone().into_inner();

    if let Some(arg_list_pair) = inner_stmt_pairs.find(|p| p.as_rule() == Rule::statement_arg_list)
    {
        let arg_list_span = get_span(&arg_list_pair);
        for arg_pair in arg_list_pair
            .into_inner()
            .filter(|p| p.as_rule() == Rule::statement_arg)
        {
            let arg_content_pair =
                arg_pair
                    .into_inner()
                    .next()
                    .ok_or_else(|| ProcessorError::MissingElement {
                        element_type: "argument content for BuilderArg".to_string(),
                        context: format!(
                            "argument in statement {} during parse_statement_args",
                            context_stmt_name
                        ),
                        span: Some(arg_list_span),
                    })?;
            let builder_arg = pest_pair_to_builder_arg(&arg_content_pair, context_stmt_name)?;
            builder_args.push(builder_arg);
        }
    }
    Ok(builder_args)
}

#[cfg(test)]
mod processor_tests {
    use std::collections::HashMap;

    use pest::iterators::Pairs;

    use super::{first_pass, second_pass, ProcessingContext};
    use crate::{
        lang::{
            error::ProcessorError,
            parser::{parse_podlog, Rule},
        },
        middleware::Params,
    };

    fn get_document_content_pairs(input: &str) -> Result<Pairs<Rule>, ProcessorError> {
        let full_parse_tree = parse_podlog(input)
            .map_err(|e| ProcessorError::Internal(format!("Test parsing failed: {:?}", e)))?;

        let document_node = full_parse_tree.peek().ok_or_else(|| {
            ProcessorError::Internal("Parser returned no pairs for the document rule.".to_string())
        })?;

        if document_node.as_rule() != Rule::document {
            return Err(ProcessorError::Internal(format!(
                "Expected top-level pair to be Rule::document, but found {:?}.",
                document_node.as_rule()
            )));
        }
        Ok(full_parse_tree.into_iter().next().unwrap().into_inner())
    }

    #[test]
    fn test_fp_empty_input() -> Result<(), ProcessorError> {
        let input = "";
        let pairs = get_document_content_pairs(input)?;
        let params = Params::default();
        let mut ctx = ProcessingContext::new(&params);
        first_pass(pairs, &mut ctx)?;
        assert!(ctx.custom_predicate_signatures.is_empty());
        assert!(ctx.custom_predicate_pairs.is_empty());
        assert!(ctx.request_pair.is_none());
        Ok(())
    }

    #[test]
    fn test_fp_only_request() -> Result<(), ProcessorError> {
        let input = "REQUEST( Equal(?A[\"k\"],?B[\"k\"]) )"; // Escaped quotes
        let pairs = get_document_content_pairs(input)?;
        let params = Params::default();
        let mut ctx = ProcessingContext::new(&params);
        first_pass(pairs, &mut ctx)?;
        assert!(ctx.custom_predicate_signatures.is_empty());
        assert!(ctx.custom_predicate_pairs.is_empty());
        assert!(ctx.request_pair.is_some());
        assert_eq!(
            ctx.request_pair.as_ref().unwrap().as_rule(),
            Rule::request_def
        );
        Ok(())
    }

    #[test]
    fn test_fp_simple_predicate() -> Result<(), ProcessorError> {
        let input = "my_pred(A, B) = AND( Equal(?A[\"k\"],?B[\"k\"]) )"; // Escaped quotes
        let pairs = get_document_content_pairs(input)?;
        let params = Params::default();
        let mut ctx = ProcessingContext::new(&params);
        first_pass(pairs, &mut ctx)?;
        assert_eq!(ctx.custom_predicate_signatures.len(), 1);
        assert_eq!(ctx.custom_predicate_pairs.len(), 1);
        assert!(ctx.request_pair.is_none());

        let (index, arity) = ctx.custom_predicate_signatures.get("my_pred").unwrap();
        assert_eq!(*index, 0);
        assert_eq!(*arity, 2); // A, B
        assert_eq!(
            ctx.custom_predicate_pairs[0].as_rule(),
            Rule::custom_predicate_def
        );
        Ok(())
    }

    #[test]
    fn test_fp_multiple_predicates() -> Result<(), ProcessorError> {
        let input = r#"
            pred1(X) = AND( Equal(?X["k"],?X["k"]) )
            pred2(Y, Z) = OR( ValueOf(?Y["v"], 123) )
        "#;
        let pairs = get_document_content_pairs(input)?;
        let params = Params::default();
        let mut ctx = ProcessingContext::new(&params);
        first_pass(pairs, &mut ctx)?;
        assert_eq!(ctx.custom_predicate_signatures.len(), 2);
        assert_eq!(ctx.custom_predicate_pairs.len(), 2);

        let (idx1, arity1) = ctx.custom_predicate_signatures.get("pred1").unwrap();
        assert_eq!(*idx1, 0);
        assert_eq!(*arity1, 1);

        let (idx2, arity2) = ctx.custom_predicate_signatures.get("pred2").unwrap();
        assert_eq!(*idx2, 1);
        assert_eq!(*arity2, 2);
        Ok(())
    }

    #[test]
    fn test_fp_predicate_public_args_count() -> Result<(), ProcessorError> {
        let inputs_and_expected_arities = vec![
            ("p1(A) = AND(None()) // One public arg", 1),
            ("p3(A,B,C) = AND(None()) // Three public args", 3),
            ("p_pub_priv(Pub1, private: Priv1) = AND(None())", 1),
        ];

        for (input_str, expected_arity) in inputs_and_expected_arities {
            let pairs = get_document_content_pairs(input_str)?;
            let params = Params::default();
            let mut ctx = ProcessingContext {
                params: &params,
                custom_predicate_signatures: HashMap::new(),
                custom_predicate_pairs: Vec::new(),
                request_pair: None,
            };
            first_pass(pairs, &mut ctx)?;
            let pred_name = ctx
                .custom_predicate_signatures
                .keys()
                .next()
                .expect("No predicate found in test string");
            let (_, arity) = ctx.custom_predicate_signatures.get(pred_name).unwrap();
            assert_eq!(*arity, expected_arity, "Mismatch for input: {}", input_str);
        }
        Ok(())
    }

    #[test]
    fn test_fp_duplicate_predicate() {
        let input = r#"
            my_pred(A) = AND(None())
            my_pred(B) = OR(None())
        "#;
        let pairs = get_document_content_pairs(input).unwrap();
        let params = Params::default();
        let mut ctx = ProcessingContext::new(&params);
        let result = first_pass(pairs, &mut ctx);
        assert!(result.is_err());
        match result.err().unwrap() {
            // Use .err().unwrap() for ProcessorError
            ProcessorError::DuplicateDefinition { name, .. } => {
                assert_eq!(name, "my_pred");
            }
            e => panic!("Expected DuplicateDefinition, got {:?}", e),
        }
    }

    #[test]
    fn test_fp_multiple_requests() {
        let input = r#"
            REQUEST(None())
            REQUEST(None())
        "#;
        let pairs = get_document_content_pairs(input).unwrap();
        let params = Params::default();
        let mut ctx = ProcessingContext::new(&params);
        let result = first_pass(pairs, &mut ctx);
        assert!(result.is_err());
        match result.err().unwrap() {
            // Use .err().unwrap() for ProcessorError
            ProcessorError::MultipleRequestDefinitions { .. } => { /* Correct error */ }
            e => panic!("Expected MultipleRequestDefinitions, got {:?}", e),
        }
    }

    #[test]
    fn test_fp_mixed_content() -> Result<(), ProcessorError> {
        let input = r#"
            pred_one(X) = AND(None())
            REQUEST( pred_one(?A) )
            pred_two(Y, Z) = OR(None())
        "#;
        let pairs = get_document_content_pairs(input)?;
        let params = Params::default();
        let mut ctx = ProcessingContext::new(&params);
        first_pass(pairs, &mut ctx)?;

        assert_eq!(ctx.custom_predicate_signatures.len(), 2);
        assert_eq!(ctx.custom_predicate_pairs.len(), 2);
        assert!(ctx.request_pair.is_some());

        let (idx1, arity1) = ctx.custom_predicate_signatures.get("pred_one").unwrap();
        assert_eq!(*idx1, 0);
        assert_eq!(*arity1, 1);

        let (idx2, arity2) = ctx.custom_predicate_signatures.get("pred_two").unwrap();
        assert_eq!(*idx2, 1);
        assert_eq!(*arity2, 2);

        // Check that the pairs were stored in the correct order and have the correct content (simplistic check)
        assert!(ctx.custom_predicate_pairs[0].as_str().contains("pred_one"));
        assert!(ctx.custom_predicate_pairs[1].as_str().contains("pred_two"));
        assert!(ctx
            .request_pair
            .as_ref()
            .unwrap()
            .as_str()
            .contains("pred_one(?A)"));

        Ok(())
    }

    #[test]
    fn test_sp_unknown_predicate() -> Result<(), ProcessorError> {
        // Undefined predicates will be flagged as an error on the second pass
        let input = r#"
            REQUEST(
              pred_one(?A)
            )
        "#;
        let pairs = get_document_content_pairs(input)?;
        let params = Params::default();
        let mut ctx = ProcessingContext::new(&params);
        first_pass(pairs, &mut ctx)?;
        let result = second_pass(&mut ctx);
        assert!(result.is_err());
        match result.err().unwrap() {
            ProcessorError::UndefinedIdentifier { name, span: _ } => {
                assert_eq!(name, "pred_one")
            }
            e => panic!("Expected UndefinedIdentifier, got {:?}", e),
        }

        // Native predicate names are case-senstive
        let input = r#"
        REQUEST(
          EQUAL(?A[?B], ?C[?D])
        )
    "#;
        let pairs = get_document_content_pairs(input)?;
        let params = Params::default();
        let mut ctx = ProcessingContext::new(&params);
        first_pass(pairs, &mut ctx)?;
        let result = second_pass(&mut ctx);
        assert!(result.is_err());
        match result.err().unwrap() {
            ProcessorError::UndefinedIdentifier { name, span: _ } => {
                assert_eq!(name, "EQUAL")
            }
            e => panic!("Expected UndefinedIdentifier, got {:?}", e),
        }

        Ok(())
    }
}
