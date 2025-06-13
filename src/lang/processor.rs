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
pub struct PodlangOutput {
    pub custom_batch: Arc<CustomPredicateBatch>,
    pub request_templates: Vec<StatementTmpl>,
}

struct ProcessingContext<'a> {
    params: &'a Params,
    /// Maps imported predicate names to their full reference (batch and index)
    imported_predicates: HashMap<String, CustomPredicateRef>,
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

    second_pass(&mut processing_ctx)
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
            Rule::use_statement => {
                process_use_statement(&pair, ctx, available_batches)?;
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

fn process_use_statement(
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

        if ctx.imported_predicates.contains_key(&name) {
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

enum StatementContext<'a> {
    CustomPredicate,
    Request {
        custom_batch: &'a Arc<CustomPredicateBatch>,
        wildcard_names: &'a mut Vec<String>,
        defined_wildcards: &'a mut HashSet<String>,
    },
}

fn second_pass(ctx: &mut ProcessingContext) -> Result<PodlangOutput, ProcessorError> {
    let mut cpb_builder =
        CustomPredicateBatchBuilder::new(ctx.params.clone(), "PodlangBatch".to_string());

    for pred_pair in &ctx.custom_predicate_pairs {
        process_and_add_custom_predicate_to_batch(pred_pair, ctx, &mut cpb_builder)?;
    }

    let custom_batch = cpb_builder.finish();

    let request_templates = if let Some(req_pair) = &ctx.request_pair {
        process_request_def(req_pair, ctx, &custom_batch)?
    } else {
        Vec::new()
    };

    Ok(PodlangOutput {
        custom_batch,
        request_templates,
    })
}

fn pest_pair_to_builder_arg(arg_content_pair: &Pair<Rule>) -> Result<BuilderArg, ProcessorError> {
    match arg_content_pair.as_rule() {
        Rule::literal_value => {
            let value = process_literal_value(arg_content_pair)?;
            Ok(BuilderArg::Literal(value))
        }
        Rule::wildcard => {
            let name = arg_content_pair.as_str().strip_prefix("?").unwrap();
            Ok(BuilderArg::WildcardLiteral(name.to_string()))
        }
        Rule::anchored_key => {
            let mut inner_ak_pairs = arg_content_pair.clone().into_inner();
            let pod_id_pair = inner_ak_pairs.next().unwrap();

            let pod_self_or_wc_str = match pod_id_pair.as_rule() {
                Rule::wildcard => {
                    let name = pod_id_pair.as_str().strip_prefix("?").unwrap();
                    SelfOrWildcardStr::Wildcard(name.to_string())
                }
                Rule::self_keyword => SelfOrWildcardStr::SELF,
                _ => {
                    unreachable!("Unexpected rule: {:?}", pod_id_pair.as_rule());
                }
            };

            let key_part_pair = inner_ak_pairs.next().unwrap();

            let key_or_wildcard_str = match key_part_pair.as_rule() {
                Rule::wildcard => {
                    let key_wildcard_name = key_part_pair.as_str().strip_prefix("?").unwrap();
                    KeyOrWildcardStr::Wildcard(key_wildcard_name.to_string())
                }
                Rule::literal_string => {
                    let key_str_literal = parse_pest_string_literal(&key_part_pair)?;
                    KeyOrWildcardStr::Key(key_str_literal)
                }
                _ => {
                    unreachable!("Unexpected rule: {:?}", key_part_pair.as_rule());
                }
            };
            Ok(BuilderArg::Key(pod_self_or_wc_str, key_or_wildcard_str))
        }
        _ => unreachable!("Unexpected rule: {:?}", arg_content_pair.as_rule()),
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
        Predicate::Custom(custom_ref) => {
            let expected_arity = custom_ref.predicate().args_len;
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
            &stmt_pair,
            processing_ctx,
            StatementContext::CustomPredicate,
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
            let built_stb = process_statement_template(
                &stmt_pair,
                processing_ctx,
                StatementContext::Request {
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
    stmt_pair: &Pair<Rule>,
    processing_ctx: &ProcessingContext,
    mut context: StatementContext,
) -> Result<StatementTmplBuilder, ProcessorError> {
    let mut inner_stmt_pairs = stmt_pair.clone().into_inner();
    let name_pair = inner_stmt_pairs
        .find(|p| p.as_rule() == Rule::identifier)
        .unwrap();
    let stmt_name_str = name_pair.as_str();

    let builder_args = parse_statement_args(stmt_pair)?;

    if let StatementContext::Request {
        wildcard_names,
        defined_wildcards,
        ..
    } = &mut context
    {
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
    } else if let Some((pred_index, _expected_arity)) = processing_ctx
        .custom_predicate_signatures
        .get(stmt_name_str)
    {
        match context {
            StatementContext::CustomPredicate => Predicate::BatchSelf(*pred_index),
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

fn process_literal_value(lit_val_pair: &Pair<Rule>) -> Result<Value, ProcessorError> {
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
                .map(|elem_pair| process_literal_value(&elem_pair))
                .collect();
            let middleware_array =
                middleware::containers::Array::new(crate::constants::MAX_DEPTH, elements?)
                    .map_err(|e| {
                        ProcessorError::Internal(format!("Failed to create Array: {}", e))
                    })?;
            Ok(Value::from(middleware_array))
        }
        Rule::literal_set => {
            let elements: Result<HashSet<Value>, ProcessorError> = inner_lit
                .into_inner()
                .map(|elem_pair| process_literal_value(&elem_pair))
                .collect();
            let middleware_set =
                middleware::containers::Set::new(crate::constants::MAX_DEPTH, elements?).map_err(
                    |e| ProcessorError::Internal(format!("Failed to create Set: {}", e)),
                )?;
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
                    let val = process_literal_value(&val_pair)?;
                    Ok((Key::new(key_str), val))
                })
                .collect();
            let middleware_dict =
                middleware::containers::Dictionary::new(crate::constants::MAX_DEPTH, pairs?)
                    .map_err(|e| {
                        ProcessorError::Internal(format!("Failed to create Dictionary: {}", e))
                    })?;
            Ok(Value::from(middleware_dict))
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

fn parse_statement_args(stmt_pair: &Pair<Rule>) -> Result<Vec<BuilderArg>, ProcessorError> {
    let mut builder_args = Vec::new();
    let mut inner_stmt_pairs = stmt_pair.clone().into_inner();

    if let Some(arg_list_pair) = inner_stmt_pairs.find(|p| p.as_rule() == Rule::statement_arg_list)
    {
        for arg_pair in arg_list_pair
            .into_inner()
            .filter(|p| p.as_rule() == Rule::statement_arg)
        {
            let arg_content_pair = arg_pair.into_inner().next().unwrap();
            let builder_arg = pest_pair_to_builder_arg(&arg_content_pair)?;
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

    fn get_document_content_pairs(input: &str) -> Result<Pairs<Rule>, ProcessorError> {
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
        let input = "REQUEST( Equal(?A[\"k\"],?B[\"k\"]) )"; // Escaped quotes
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
        let input = "my_pred(A, B) = AND( Equal(?A[\"k\"],?B[\"k\"]) )"; // Escaped quotes
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
            pred1(X) = AND( Equal(?X["k"],?X["k"]) )
            pred2(Y, Z) = OR( ValueOf(?Y["v"], 123) )
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
            REQUEST( pred_one(?A) )
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
        first_pass(pairs, &mut ctx, &[])?;
        let result = second_pass(&mut ctx);
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
          EQUAL(?A[?B], ?C[?D])
        )
    "#;
        let pairs = get_document_content_pairs(input)?;
        let params = Params::default();
        let mut ctx = ProcessingContext::new(&params);
        first_pass(pairs, &mut ctx, &[])?;
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
