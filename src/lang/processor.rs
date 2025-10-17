use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use pest::iterators::{Pair, Pairs};
use plonky2::field::types::Field;

use super::error::ProcessorError;
use crate::{
    backends::plonky2::{
        deserialize_bytes,
        primitives::ec::{curve::Point, schnorr::SecretKey},
    },
    frontend::{BuilderArg, CustomPredicateBatchBuilder, PodRequest, StatementTmplBuilder},
    lang::parser::Rule,
    middleware::{
        self, CustomPredicateBatch, CustomPredicateRef, Hash, IntroPredicateRef, Key,
        NativePredicate, Params, Predicate, StatementTmpl, StatementTmplArg, Value, Wildcard, F,
        VALUE_SIZE,
    },
};

fn get_span(pair: &Pair<Rule>) -> (usize, usize) {
    let span = pair.as_span();
    (span.start(), span.end())
}

pub fn native_predicate_from_string(s: &str) -> Option<NativePredicate> {
    match s {
        // TODO: update any code that still uses ValueOf to use Equal instead
        "ValueOf" => Some(NativePredicate::Equal),
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
        "PublicKeyOf" => Some(NativePredicate::PublicKeyOf),
        "SignedBy" => Some(NativePredicate::SignedBy),
        "ContainerInsert" => Some(NativePredicate::ContainerInsert),
        "ContainerUpdate" => Some(NativePredicate::ContainerUpdate),
        "ContainerDelete" => Some(NativePredicate::ContainerDelete),
        "DictContains" => Some(NativePredicate::DictContains),
        "DictNotContains" => Some(NativePredicate::DictNotContains),
        "ArrayContains" => Some(NativePredicate::ArrayContains),
        "SetContains" => Some(NativePredicate::SetContains),
        "SetNotContains" => Some(NativePredicate::SetNotContains),
        "DictInsert" => Some(NativePredicate::DictInsert),
        "DictUpdate" => Some(NativePredicate::DictUpdate),
        "DictDelete" => Some(NativePredicate::DictDelete),
        "SetInsert" => Some(NativePredicate::SetInsert),
        "SetDelete" => Some(NativePredicate::SetDelete),
        "ArrayUpdate" => Some(NativePredicate::ArrayUpdate),
        "None" => Some(NativePredicate::None),
        "False" => Some(NativePredicate::False),
        _ => None,
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct PodlangOutput {
    pub custom_batch: Arc<CustomPredicateBatch>,
    pub request: PodRequest,
}

struct ProcessingContext<'a> {
    params: &'a Params,
    /// Maps imported predicate names to their full reference (batch and index)
    imported_predicates: HashMap<String, CustomPredicateRef>,
    /// Maps imported intro predicate names to their intro refs
    imported_intro_predicates: HashMap<String, IntroPredicateRef>,
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
            imported_predicates: HashMap::new(),
            imported_intro_predicates: HashMap::new(),
            custom_predicate_signatures: HashMap::new(),
            custom_predicate_pairs: Vec::new(),
            request_pair: None,
        }
    }
}

pub fn process_pest_tree(
    mut pairs_iterator_for_document_rule: Pairs<'_, Rule>,
    params: &Params,
    available_batches: &[Arc<CustomPredicateBatch>],
) -> Result<PodlangOutput, ProcessorError> {
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

    first_pass(
        document_content_pairs,
        &mut processing_ctx,
        available_batches,
    )?;

    second_pass(&mut processing_ctx, params)
}

/// Pass 1: Iterates through top-level definitions, records custom predicate
/// signatures and stores pairs for Pass 2.
fn first_pass<'a>(
    document_pairs: Pairs<'a, Rule>,
    ctx: &mut ProcessingContext<'a>,
    available_batches: &[Arc<CustomPredicateBatch>],
) -> Result<(), ProcessorError> {
    let mut defined_custom_names: HashSet<String> = HashSet::new();
    let mut first_request_span: Option<(usize, usize)> = None;

    for pair in document_pairs {
        match pair.as_rule() {
            Rule::use_batch_statement => {
                process_use_batch_statement(&pair, ctx, available_batches)?;
            }
            Rule::use_intro_statement => {
                process_use_intro_statement(&pair, ctx)?;
            }
            Rule::custom_predicate_def => {
                let pred_name_pair = pair
                    .clone()
                    .into_inner()
                    .find(|p| p.as_rule() == Rule::identifier)
                    .unwrap();
                let pred_name = pred_name_pair.as_str().to_string();

                if defined_custom_names.contains(&pred_name)
                    || ctx.imported_predicates.contains_key(&pred_name)
                    || ctx.imported_intro_predicates.contains_key(&pred_name)
                {
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
                unreachable!("Unexpected rule: {:?}", pair.as_rule());
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
        .unwrap();

    let public_arg_list_pair = arg_section_pair
        .into_inner()
        .find(|p| p.as_rule() == Rule::public_arg_list)
        .unwrap();

    Ok(public_arg_list_pair
        .into_inner()
        .filter(|p| p.as_rule() == Rule::identifier)
        .count())
}

fn process_use_batch_statement(
    use_pair: &Pair<Rule>,
    ctx: &mut ProcessingContext,
    available_batches: &[Arc<CustomPredicateBatch>],
) -> Result<(), ProcessorError> {
    let mut inner = use_pair.clone().into_inner();

    let import_list_pair = inner
        .find(|p| p.as_rule() == Rule::use_predicate_list)
        .unwrap();
    let batch_ref_pair = inner.find(|p| p.as_rule() == Rule::batch_ref).unwrap();
    let batch_id_pair = batch_ref_pair.into_inner().next().unwrap();
    let batch_id_str_full = batch_id_pair.as_str();

    let batch_id_hex = batch_id_str_full
        .strip_prefix("0x")
        .unwrap_or(batch_id_str_full);
    let batch_id_val = parse_hex_str_to_raw_value(batch_id_hex).map_err(|_| {
        ProcessorError::InvalidLiteralFormat {
            kind: "batch ID hash".to_string(),
            value: batch_id_str_full.to_string(),
            span: Some(get_span(&batch_id_pair)),
        }
    })?;

    let target_batch = available_batches
        .iter()
        .find(|b| b.id().0 == batch_id_val.0)
        .ok_or_else(|| ProcessorError::BatchNotFound {
            id: batch_id_str_full.to_string(),
            span: Some(get_span(&batch_id_pair)),
        })?;

    let import_names: Vec<Pair<Rule>> = import_list_pair
        .into_inner()
        .filter(|p| p.as_rule() == Rule::import_name)
        .collect();

    if import_names.len() != target_batch.predicates().len() {
        return Err(ProcessorError::ImportArityMismatch {
            expected: target_batch.predicates().len(),
            found: import_names.len(),
            span: Some(get_span(use_pair)),
        });
    }

    for (i, import_name_pair) in import_names.into_iter().enumerate() {
        if import_name_pair.as_str() == "_" {
            continue;
        }

        let name = import_name_pair.as_str().to_string();

        if ctx.imported_predicates.contains_key(&name)
            || ctx.imported_intro_predicates.contains_key(&name)
            || ctx.custom_predicate_signatures.contains_key(&name)
        {
            return Err(ProcessorError::DuplicateImportName {
                name,
                span: Some(get_span(&import_name_pair)),
            });
        }

        let custom_pred_ref = CustomPredicateRef::new(target_batch.clone(), i);
        ctx.imported_predicates.insert(name, custom_pred_ref);
    }

    Ok(())
}

fn process_use_intro_statement(
    use_pair: &Pair<Rule>,
    ctx: &mut ProcessingContext,
) -> Result<(), ProcessorError> {
    let mut inner = use_pair.clone().into_inner();

    // Structure: identifier, '(', optional arg list, ')', 'from', batch_ref
    let name_pair = inner.find(|p| p.as_rule() == Rule::identifier).unwrap();
    let pred_name = name_pair.as_str().to_string();

    if ctx.imported_predicates.contains_key(&pred_name)
        || ctx.imported_intro_predicates.contains_key(&pred_name)
        || ctx.custom_predicate_signatures.contains_key(&pred_name)
    {
        return Err(ProcessorError::DuplicateImportName {
            name: pred_name,
            span: Some(get_span(&name_pair)),
        });
    }

    let args_len = inner
        .clone()
        .find(|p| p.as_rule() == Rule::use_intro_arg_list)
        .map(|arg_list| {
            arg_list
                .into_inner()
                .filter(|p| p.as_rule() == Rule::identifier)
                .count()
        })
        .unwrap_or(0);

    let batch_ref_pair = inner.find(|p| p.as_rule() == Rule::batch_ref).unwrap();
    let hash_hex_pair = batch_ref_pair.into_inner().next().unwrap();
    let hash_str_full = hash_hex_pair.as_str();
    let hex_no_prefix = hash_str_full.strip_prefix("0x").unwrap_or(hash_str_full);
    let raw_val = parse_hex_str_to_raw_value(hex_no_prefix).map_err(|_| {
        ProcessorError::InvalidLiteralFormat {
            kind: "intro verifier hash".to_string(),
            value: hash_str_full.to_string(),
            span: Some(get_span(&hash_hex_pair)),
        }
    })?;
    let verifier_hash: Hash = Hash::from(raw_val);

    let intro_ref = IntroPredicateRef {
        name: pred_name.clone(),
        args_len,
        verifier_data_hash: verifier_hash,
    };

    ctx.imported_intro_predicates.insert(pred_name, intro_ref);

    Ok(())
}

enum StatementContext<'a> {
    CustomPredicate {
        pred_name: &'a str,
        argument_names: &'a HashSet<String>,
    },
    Request {
        custom_batch: &'a Arc<CustomPredicateBatch>,
        wildcard_names: &'a mut Vec<String>,
        defined_wildcards: &'a mut HashSet<String>,
    },
}

fn second_pass(
    ctx: &mut ProcessingContext,
    params: &Params,
) -> Result<PodlangOutput, ProcessorError> {
    let mut cpb_builder =
        CustomPredicateBatchBuilder::new(ctx.params.clone(), "PodlangBatch".to_string());

    for pred_pair in &ctx.custom_predicate_pairs {
        process_and_add_custom_predicate_to_batch(params, pred_pair, ctx, &mut cpb_builder)?;
    }

    let custom_batch = cpb_builder.finish();

    let request_templates = if let Some(req_pair) = &ctx.request_pair {
        process_request_def(params, req_pair, ctx, &custom_batch)?
    } else {
        Vec::new()
    };

    Ok(PodlangOutput {
        custom_batch,
        request: PodRequest::new(request_templates),
    })
}

fn pest_pair_to_builder_arg(
    params: &Params,
    arg_content_pair: &Pair<Rule>,
    context: &StatementContext,
) -> Result<BuilderArg, ProcessorError> {
    match arg_content_pair.as_rule() {
        Rule::literal_value => {
            let value = process_literal_value(params, arg_content_pair)?;
            Ok(BuilderArg::Literal(value))
        }
        Rule::identifier => {
            let wc_str = arg_content_pair.as_str();
            if let StatementContext::CustomPredicate {
                argument_names,
                pred_name,
            } = context
            {
                if !argument_names.contains(wc_str) {
                    return Err(ProcessorError::UndefinedWildcard {
                        name: wc_str.to_string(),
                        pred_name: pred_name.to_string(),
                        span: Some(get_span(arg_content_pair)),
                    });
                }
            }
            Ok(BuilderArg::WildcardLiteral(wc_str.to_string()))
        }
        Rule::anchored_key => {
            let mut inner_ak_pairs = arg_content_pair.clone().into_inner();
            let root_pair = inner_ak_pairs.next().unwrap();
            let root_wc_str = root_pair.as_str();

            if let StatementContext::CustomPredicate {
                argument_names,
                pred_name,
            } = context
            {
                if !argument_names.contains(root_wc_str) {
                    return Err(ProcessorError::UndefinedWildcard {
                        name: root_wc_str.to_string(),
                        pred_name: pred_name.to_string(),
                        span: Some(get_span(arg_content_pair)),
                    });
                }
            }

            let key_part_pair = inner_ak_pairs.next().unwrap();
            let key_str = match key_part_pair.as_rule() {
                Rule::literal_string => parse_pest_string_literal(&key_part_pair)?,
                Rule::identifier => key_part_pair.as_str().to_string(),
                _ => unreachable!(
                    "unknown key type in anchored key: {:?}",
                    key_part_pair.as_rule()
                ),
            };
            Ok(BuilderArg::Key(root_wc_str.to_string(), key_str))
        }
        _ => unreachable!("Unexpected rule: {:?}", arg_content_pair.as_rule()),
    }
}

fn validate_dyn_len_predicate(
    stmt_name_str: &str,
    args: &[BuilderArg],
    expected_arity: usize,
    stmt_span: (usize, usize),
    stmt_name_span: (usize, usize),
) -> Result<(), ProcessorError> {
    if args.len() != expected_arity {
        return Err(ProcessorError::ArgumentCountMismatch {
            predicate: stmt_name_str.to_string(),
            expected: expected_arity,
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
    Ok(())
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
            let expected_arity = match native_pred {
                NativePredicate::Gt
                | NativePredicate::GtEq
                | NativePredicate::Equal
                | NativePredicate::NotEqual
                | NativePredicate::Lt
                | NativePredicate::LtEq
                | NativePredicate::SetContains
                | NativePredicate::DictNotContains
                | NativePredicate::SetNotContains
                | NativePredicate::NotContains
                | NativePredicate::PublicKeyOf
                | NativePredicate::SignedBy => 2,
                NativePredicate::Contains
                | NativePredicate::ArrayContains
                | NativePredicate::DictContains
                | NativePredicate::SumOf
                | NativePredicate::ProductOf
                | NativePredicate::MaxOf
                | NativePredicate::HashOf
                | NativePredicate::ContainerDelete
                | NativePredicate::DictDelete
                | NativePredicate::SetInsert
                | NativePredicate::SetDelete => 3,
                NativePredicate::ContainerInsert
                | NativePredicate::ContainerUpdate
                | NativePredicate::DictInsert
                | NativePredicate::DictUpdate
                | NativePredicate::ArrayUpdate => 4,
                NativePredicate::None | NativePredicate::False => 0,
            };

            if args.len() != expected_arity {
                return Err(ProcessorError::ArgumentCountMismatch {
                    predicate: stmt_name_str.to_string(),
                    expected: expected_arity,
                    found: args.len(),
                    span: Some(stmt_name_span),
                });
            }
        }
        Predicate::Custom(custom_ref) => {
            let expected_arity = custom_ref.predicate().args_len;
            validate_dyn_len_predicate(
                stmt_name_str,
                &args,
                expected_arity,
                stmt_span,
                stmt_name_span,
            )?;
        }
        Predicate::Intro(intro_ref) => {
            let expected_arity = intro_ref.args_len;
            validate_dyn_len_predicate(
                stmt_name_str,
                &args,
                expected_arity,
                stmt_span,
                stmt_name_span,
            )?;
        }
        Predicate::BatchSelf(_) => {
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
    params: &Params,
    pred_def_pair: &Pair<Rule>,
    processing_ctx: &ProcessingContext,
    cpb_builder: &mut CustomPredicateBatchBuilder,
) -> Result<(), ProcessorError> {
    let mut inner_pairs = pred_def_pair.clone().into_inner();
    let name_pair = inner_pairs
        .find(|p| p.as_rule() == Rule::identifier)
        .unwrap();
    let name = name_pair.as_str().to_string();

    let arg_section_pair = inner_pairs
        .find(|p| p.as_rule() == Rule::arg_section)
        .unwrap();

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
                unreachable!("Unexpected rule: {:?}", arg_part_pair.as_rule());
            }
        }
    }

    let conjunction_type_pair = inner_pairs
        .find(|p| p.as_rule() == Rule::conjunction_type)
        .unwrap();
    let conjunction = match conjunction_type_pair.as_str() {
        "AND" => true,
        "OR" => false,
        _ => {
            unreachable!(
                "Invalid conjunction type: {}",
                conjunction_type_pair.as_str()
            );
        }
    };

    let statement_list_pair = inner_pairs
        .find(|p| p.as_rule() == Rule::statement_list)
        .unwrap_or_else(|| {
            unreachable!("statement_list rule must be present in predicate definition")
        });

    let mut statement_builders = Vec::new();
    for stmt_pair in statement_list_pair
        .into_inner()
        .filter(|p| p.as_rule() == Rule::statement)
    {
        let stb = process_statement_template(
            params,
            &stmt_pair,
            processing_ctx,
            &mut StatementContext::CustomPredicate {
                pred_name: &name,
                argument_names: &defined_arg_names,
            },
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
    params: &Params,
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
            let built_stb = process_statement_template(
                params,
                &stmt_pair,
                processing_ctx,
                &mut StatementContext::Request {
                    custom_batch,
                    wildcard_names: &mut request_wildcard_names,
                    defined_wildcards: &mut defined_request_wildcards,
                },
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

    Ok(request_templates)
}

fn process_statement_template(
    params: &Params,
    stmt_pair: &Pair<Rule>,
    processing_ctx: &ProcessingContext,
    context: &mut StatementContext,
) -> Result<StatementTmplBuilder, ProcessorError> {
    let mut inner_stmt_pairs = stmt_pair.clone().into_inner();
    let name_pair = inner_stmt_pairs
        .find(|p| p.as_rule() == Rule::identifier)
        .unwrap();
    let stmt_name_str = name_pair.as_str();

    let builder_args = parse_statement_args(params, stmt_pair, context)?;

    if let StatementContext::Request {
        wildcard_names,
        defined_wildcards,
        ..
    } = context
    {
        let mut temp_stmt_wildcard_names: Vec<String> = Vec::new();
        for arg in &builder_args {
            match arg {
                BuilderArg::WildcardLiteral(name) => temp_stmt_wildcard_names.push(name.clone()),
                BuilderArg::Key(root_wc_str, _key_str) => {
                    temp_stmt_wildcard_names.push(root_wc_str.clone());
                }
                _ => {}
            }
        }
        for name in temp_stmt_wildcard_names {
            if defined_wildcards.insert(name.clone()) {
                wildcard_names.push(name);
            }
        }
    }

    let middleware_predicate_type = if let Some(native_pred) =
        native_predicate_from_string(stmt_name_str)
    {
        Predicate::Native(native_pred)
    } else if let Some(custom_ref) = processing_ctx.imported_predicates.get(stmt_name_str) {
        Predicate::Custom(custom_ref.clone())
    } else if let Some(intro_ref) = processing_ctx.imported_intro_predicates.get(stmt_name_str) {
        Predicate::Intro(intro_ref.clone())
    } else if let Some((pred_index, _expected_arity)) = processing_ctx
        .custom_predicate_signatures
        .get(stmt_name_str)
    {
        match context {
            StatementContext::CustomPredicate { .. } => Predicate::BatchSelf(*pred_index),
            StatementContext::Request { custom_batch, .. } => {
                let custom_pred_ref = CustomPredicateRef::new(custom_batch.clone(), *pred_index);
                Predicate::Custom(custom_pred_ref)
            }
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
    params: &Params,
    lit_val_pair: &Pair<Rule>,
) -> Result<Value, ProcessorError> {
    let inner_lit = lit_val_pair.clone().into_inner().next().unwrap();

    match inner_lit.as_rule() {
        Rule::literal_int => {
            let val = inner_lit.as_str().parse::<i64>().unwrap();
            Ok(Value::from(val))
        }
        Rule::literal_bool => {
            let val = inner_lit.as_str().parse::<bool>().unwrap();
            Ok(Value::from(val))
        }
        Rule::literal_raw => {
            let full_literal_str = inner_lit.clone().into_inner().next().unwrap();
            let hex_str_no_prefix = full_literal_str
                .as_str()
                .strip_prefix("0x")
                .unwrap_or(full_literal_str.as_str());
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
        Rule::literal_public_key => {
            let pk_str_pair = inner_lit.into_inner().next().unwrap();
            let pk_b58 = pk_str_pair.as_str();
            let point: Point =
                pk_b58
                    .parse()
                    .map_err(|e| ProcessorError::InvalidLiteralFormat {
                        kind: "PublicKey".to_string(),
                        value: format!("{} (error: {})", pk_b58, e),
                        span: Some(get_span(&pk_str_pair)),
                    })?;
            Ok(Value::from(point))
        }
        Rule::literal_string => Ok(Value::from(parse_pest_string_literal(&inner_lit)?)),
        Rule::literal_array => {
            let elements: Result<Vec<Value>, ProcessorError> = inner_lit
                .into_inner()
                .map(|elem_pair| process_literal_value(params, &elem_pair))
                .collect();
            let middleware_array =
                middleware::containers::Array::new(params.max_depth_mt_containers, elements?)
                    .map_err(|e| {
                        ProcessorError::Internal(format!("Failed to create Array: {}", e))
                    })?;
            Ok(Value::from(middleware_array))
        }
        Rule::literal_set => {
            let elements: Result<HashSet<Value>, ProcessorError> = inner_lit
                .into_inner()
                .map(|elem_pair| process_literal_value(params, &elem_pair))
                .collect();
            let middleware_set =
                middleware::containers::Set::new(params.max_depth_mt_containers, elements?)
                    .map_err(|e| {
                        ProcessorError::Internal(format!("Failed to create Set: {}", e))
                    })?;
            Ok(Value::from(middleware_set))
        }
        Rule::literal_dict => {
            let pairs: Result<HashMap<Key, Value>, ProcessorError> = inner_lit
                .into_inner()
                .map(|dict_entry_pair| {
                    let mut entry_inner = dict_entry_pair.clone().into_inner();
                    let key_pair = entry_inner.next().unwrap();
                    let val_pair = entry_inner.next().unwrap();
                    let key_str = parse_pest_string_literal(&key_pair)?;
                    let val = process_literal_value(params, &val_pair)?;
                    Ok((Key::new(key_str), val))
                })
                .collect();
            let middleware_dict =
                middleware::containers::Dictionary::new(params.max_depth_mt_containers, pairs?)
                    .map_err(|e| {
                        ProcessorError::Internal(format!("Failed to create Dictionary: {}", e))
                    })?;
            Ok(Value::from(middleware_dict))
        }
        Rule::literal_secret_key => {
            let sk_str_pair = inner_lit.clone().into_inner().next().unwrap();
            let sk_base64 = sk_str_pair.as_str();
            let bytes = deserialize_bytes(sk_base64).map_err(|_e| {
                ProcessorError::InvalidLiteralFormat {
                    kind: "SecretKey".to_string(),
                    value: sk_base64.to_string(),
                    span: Some(get_span(&inner_lit)),
                }
            })?;
            let secret_key = SecretKey::from_bytes(&bytes).map_err(|_e| {
                ProcessorError::InvalidLiteralFormat {
                    kind: "SecretKey".to_string(),
                    value: sk_base64.to_string(),
                    span: Some(get_span(&inner_lit)),
                }
            })?;
            Ok(Value::from(secret_key))
        }
        _ => unreachable!("Unexpected rule: {:?}", inner_lit.as_rule()),
    }
}

fn parse_pest_string_literal(pair: &Pair<Rule>) -> Result<String, ProcessorError> {
    let inner_pair = pair.clone().into_inner().next().unwrap();

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

// Translates a big-endian hex string to a little-endian RawValue
fn parse_hex_str_to_raw_value(hex_str: &str) -> Result<middleware::RawValue, ProcessorError> {
    let mut v = [F::ZERO; VALUE_SIZE];
    let value_range = 0..VALUE_SIZE;
    for i in value_range {
        let start_idx = i * 16;
        let end_idx = start_idx + 16;
        let hex_part = &hex_str[start_idx..end_idx];

        let u64_val = u64::from_str_radix(hex_part, 16).unwrap();
        v[VALUE_SIZE - i - 1] = F::from_canonical_u64(u64_val);
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
            pred_name: "REQUEST".to_string(),
            span: None,
        })
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
            BuilderArg::Key(root_wc_str, key_str) => {
                let root_wc = resolve_wildcard(ordered_request_wildcard_names, &root_wc_str)?;
                let key = Key::from(key_str);
                StatementTmplArg::AnchoredKey(root_wc, key)
            }
            BuilderArg::WildcardLiteral(wc_name) => {
                let wc = resolve_wildcard(ordered_request_wildcard_names, &wc_name)?;
                StatementTmplArg::Wildcard(wc)
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
    params: &Params,
    stmt_pair: &Pair<Rule>,
    context: &StatementContext,
) -> Result<Vec<BuilderArg>, ProcessorError> {
    let mut builder_args = Vec::new();
    let mut inner_stmt_pairs = stmt_pair.clone().into_inner();

    if let Some(arg_list_pair) = inner_stmt_pairs.find(|p| p.as_rule() == Rule::statement_arg_list)
    {
        for arg_pair in arg_list_pair
            .into_inner()
            .filter(|p| p.as_rule() == Rule::statement_arg)
        {
            let arg_content_pair = arg_pair.into_inner().next().unwrap();
            let builder_arg = pest_pair_to_builder_arg(params, &arg_content_pair, context)?;
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
            parser::{parse_podlang, Rule},
        },
        middleware::Params,
    };

    fn get_document_content_pairs(input: &str) -> Result<Pairs<'_, Rule>, ProcessorError> {
        let full_parse_tree = parse_podlang(input)
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
        first_pass(pairs, &mut ctx, &[])?;
        assert!(ctx.custom_predicate_signatures.is_empty());
        assert!(ctx.custom_predicate_pairs.is_empty());
        assert!(ctx.request_pair.is_none());
        Ok(())
    }

    #[test]
    fn test_fp_only_request() -> Result<(), ProcessorError> {
        let input = "REQUEST( Equal(A[\"k\"],B.k) )"; // Escaped quotes
        let pairs = get_document_content_pairs(input)?;
        let params = Params::default();
        let mut ctx = ProcessingContext::new(&params);
        first_pass(pairs, &mut ctx, &[])?;
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
        let input = "my_pred(A, B) = AND( Equal(A[\"k\"],B.k) )"; // Escaped quotes
        let pairs = get_document_content_pairs(input)?;
        let params = Params::default();
        let mut ctx = ProcessingContext::new(&params);
        first_pass(pairs, &mut ctx, &[])?;
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
            pred1(X) = AND( Equal(X["k"],X.k) )
            pred2(Y, Z) = OR( Equal(Y["v"], 123) )
        "#;
        let pairs = get_document_content_pairs(input)?;
        let params = Params::default();
        let mut ctx = ProcessingContext::new(&params);
        first_pass(pairs, &mut ctx, &[])?;
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
                imported_predicates: HashMap::new(),
                imported_intro_predicates: HashMap::new(),
                custom_predicate_signatures: HashMap::new(),
                custom_predicate_pairs: Vec::new(),
                request_pair: None,
            };
            first_pass(pairs, &mut ctx, &[])?;
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
        let result = first_pass(pairs, &mut ctx, &[]);
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
        let result = first_pass(pairs, &mut ctx, &[]);
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
            REQUEST( pred_one(A) )
            pred_two(Y, Z) = OR(None())
        "#;
        let pairs = get_document_content_pairs(input)?;
        let params = Params::default();
        let mut ctx = ProcessingContext::new(&params);
        first_pass(pairs, &mut ctx, &[])?;

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
            .contains("pred_one(A)"));

        Ok(())
    }

    #[test]
    fn test_sp_unknown_predicate() -> Result<(), ProcessorError> {
        // Undefined predicates will be flagged as an error on the second pass
        let input = r#"
            REQUEST(
              pred_one(A)
            )
        "#;
        let pairs = get_document_content_pairs(input)?;
        let params = Params::default();
        let mut ctx = ProcessingContext::new(&params);
        first_pass(pairs, &mut ctx, &[])?;
        let result = second_pass(&mut ctx, &params);
        assert!(result.is_err());
        match result.err().unwrap() {
            ProcessorError::UndefinedIdentifier { name, span: _ } => {
                assert_eq!(name, "pred_one")
            }
            e => panic!("Expected UndefinedIdentifier, got {:?}", e),
        }

        // Native predicate names are case-sensitive
        let input = r#"
        REQUEST(
          EQUAL(A["b"], C.d)
        )
    "#;
        let pairs = get_document_content_pairs(input)?;
        let params = Params::default();
        let mut ctx = ProcessingContext::new(&params);
        first_pass(pairs, &mut ctx, &[])?;
        let result = second_pass(&mut ctx, &params);
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
