use std::collections::{HashMap, HashSet};

use anyhow::Result;
use axum::{extract::State, http::StatusCode, response::IntoResponse, Json};
use chrono::Utc;
use hex::ToHex;
use log::info;
use rusqlite::{params, OptionalExtension};
use serde::Serialize;
use serde_json::Value;

use super::pod_management::{PodData, PodInfo};
use crate::{
    backends::plonky2::{primitives::signature::SecretKey, signedpod::Signer},
    frontend::{serialization::SerializedSignedPod, MainPod, SignedPod, SignedPodBuilder},
    lang::{self, ast, parser, LangError},
    middleware::{containers::Set, Params, Pod, PodId, RawValue, Value as PodValue},
    prover::{
        self, custom_definitions_from_batches, facts_from_pods, pod_building, solver,
        ProverError as ActualProverError,
    },
    server::{
        api_types::{
            Diagnostic, DiagnosticSeverity, ExecuteCodeRequest, ExecuteMvpRequest,
            ValidateCodeRequest, ValidateCodeResponse,
        },
        db::ConnectionPool,
    },
};

#[derive(Serialize)]
pub struct ExecuteResult {
    main_pod: MainPod,
    diagram: String,
}

// --- Playground API Handlers ---

pub async fn validate_code_handler(
    Json(payload): Json<ValidateCodeRequest>,
) -> Result<Json<ValidateCodeResponse>, PlaygroundApiError> {
    log::debug!(
        "Received validate_code request for code starting with: {:?}",
        payload.code.chars().take(50).collect::<String>()
    );

    let params = Params::default();
    pest::set_error_detail(true);
    match lang::parse(&payload.code, &params) {
        Ok(_) => Ok(Json(ValidateCodeResponse {
            diagnostics: vec![],
        })),
        Err(lang_error) => {
            println!("LangError: {:?}", lang_error);
            let diagnostics = lang_error_to_diagnostics(&lang_error, &payload.code);
            Ok(Json(ValidateCodeResponse { diagnostics }))
        }
    }
}

fn lang_error_to_diagnostics(lang_error: &LangError, code: &str) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    let (message, start_line, start_col, end_line, end_col) = match lang_error {
        LangError::Parse(parse_error_box) => {
            let parser::ParseError::Pest(pest_error) = &**parse_error_box;
            let (sl, sc, el, ec) = match pest_error.line_col {
                pest::error::LineColLocation::Pos((l, c)) => (l, c, l, c),
                pest::error::LineColLocation::Span((sl, sc), (el, ec)) => (sl, sc, el, ec),
            };
            (format!("{}", pest_error.variant.message()), sl, sc, el, ec)
        }
        LangError::AstBuild(ast_build_error_box) => {
            let ast_build_error = &**ast_build_error_box;
            let actual_span_option: Option<(usize, usize)> = match ast_build_error {
                ast::AstBuildError::Generic { span, .. } => *span,
                ast::AstBuildError::UnexpectedRule { span, .. } => *span,
                ast::AstBuildError::InvalidLiteralFormat { span, .. } => *span,
                ast::AstBuildError::InvalidHexLength { span, .. } => *span,
                ast::AstBuildError::Internal(_) => None,
            };

            let (sl, sc, el, ec) = if let Some(actual_span) = actual_span_option {
                byte_span_to_line_col_span(code, actual_span.0, actual_span.1)
            } else {
                (1, 1, 1, 1)
            };
            (format!("{}", ast_build_error), sl, sc, el, ec)
        }
        LangError::Processor(processor_error_box) => {
            let processor_error = &**processor_error_box;
            (format!("{}", processor_error), 1, 1, 1, 1)
        }
        LangError::Processing(message) => (message.clone(), 1, 1, 1, 1),
        LangError::Middleware(middleware_error_box) => {
            let middleware_error = &**middleware_error_box;
            (format!("{}", middleware_error), 1, 1, 1, 1)
        }
    };

    diagnostics.push(Diagnostic {
        message,
        severity: DiagnosticSeverity::Error,
        start_line,
        start_column: start_col,
        end_line,
        end_column: end_col,
    });

    diagnostics
}

fn byte_span_to_line_col_span(
    code: &str,
    start_byte: usize,
    end_byte: usize,
) -> (usize, usize, usize, usize) {
    let mut current_byte = 0;
    let mut line = 1;
    let mut col = 1;
    let mut start_line_col = (1, 1);
    let mut end_line_col = (1, 1);
    let mut found_start = false;

    for (byte_offset, char_val) in code.char_indices() {
        if !found_start && byte_offset >= start_byte {
            start_line_col = (line, col);
            found_start = true;
        }
        if byte_offset >= end_byte {
            end_line_col = (line, col);
            break;
        }

        current_byte = byte_offset + char_val.len_utf8();

        if char_val == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }

        if current_byte >= code.len() {
            end_line_col = (line, col);
            break;
        }
    }

    if !found_start && start_byte >= code.len() {
        start_line_col = (line, col);
    }
    if current_byte < end_byte && current_byte == code.len() {
        end_line_col = (line, col);
    }

    (
        start_line_col.0,
        start_line_col.1,
        end_line_col.0,
        end_line_col.1,
    )
}

pub async fn execute_mvp_handler(
    Json(payload): Json<ExecuteMvpRequest>,
) -> Result<Json<MainPod>, PlaygroundApiError> {
    log::debug!(
        "Received execute_mvp_handler request for code starting with: {:?}",
        payload.code.chars().take(50).collect::<String>()
    );

    pest::set_error_detail(true);
    let params = Params {
        // Currently the circuit uses random access that only supports vectors of length 64.
        // With max_input_main_pods=3 we need random access to a vector of length 73.
        max_input_main_pods: 1,
        ..Default::default()
    };

    let processed_output = lang::parse(&payload.code, &params)?;

    let mut gov_signer = Signer(SecretKey(RawValue::from(1)));
    let mut pay_signer = Signer(SecretKey(RawValue::from(2)));
    let mut sanction_signer = Signer(SecretKey(RawValue::from(3)));

    let sanctions_values: HashSet<PodValue> =
        ["A343434340"].iter().map(|s| PodValue::from(*s)).collect();
    let sanction_set = PodValue::from(Set::new(sanctions_values).unwrap());

    let mut gov_id = SignedPodBuilder::new(&params);
    gov_id.insert("idNumber", "4242424242");
    gov_id.insert("dateOfBirth", 1169909384);
    gov_id.insert("socialSecurityNumber", "G2121210");

    let mut pay_stub = SignedPodBuilder::new(&params);
    pay_stub.insert("socialSecurityNumber", "G2121210");
    pay_stub.insert("startDate", 1706367566);

    let mut sanction_list = SignedPodBuilder::new(&params);
    sanction_list.insert("sanctionList", sanction_set);

    let gov_id_pod = gov_id.sign(&mut gov_signer).map_err(|e| {
        PlaygroundApiError::Internal(anyhow::Error::from(e).context("Failed to sign gov_id_pod"))
    })?;
    let pay_stub_pod = pay_stub.sign(&mut pay_signer).map_err(|e| {
        PlaygroundApiError::Internal(anyhow::Error::from(e).context("Failed to sign pay_stub_pod"))
    })?;
    let sanction_list_pod = sanction_list.sign(&mut sanction_signer).map_err(|e| {
        PlaygroundApiError::Internal(
            anyhow::Error::from(e).context("Failed to sign sanction_list_pod"),
        )
    })?;

    let all_pods_for_facts: Vec<&Box<dyn Pod>> =
        vec![&gov_id_pod.pod, &pay_stub_pod.pod, &sanction_list_pod.pod];
    let initial_facts = facts_from_pods(&all_pods_for_facts);

    let custom_definitions =
        custom_definitions_from_batches(&[processed_output.custom_batch], &params);
    let request_templates = processed_output.request_templates;

    let solution = solver::solve(
        &request_templates,
        &initial_facts,
        &params,
        &custom_definitions,
    )?;

    let mut original_signed_pods = HashMap::new();
    original_signed_pods.insert(gov_id_pod.id(), &gov_id_pod);
    original_signed_pods.insert(pay_stub_pod.id(), &pay_stub_pod);
    original_signed_pods.insert(sanction_list_pod.id(), &sanction_list_pod);

    let original_main_pods = HashMap::new();

    let main_pod = pod_building::build_main_pod_from_solution(
        &solution,
        &original_signed_pods,
        &original_main_pods,
        &params,
        &request_templates,
    )?;

    Ok(Json(main_pod))
}

pub async fn execute_code_handler(
    State(pool): State<ConnectionPool>,
    Json(payload): Json<ExecuteCodeRequest>,
) -> Result<Json<ExecuteResult>, PlaygroundApiError> {
    log::debug!(
        "Received execute_code request for space '{}' with code starting with: {:?}",
        payload.space_id,
        payload.code.chars().take(50).collect::<String>()
    );

    pest::set_error_detail(true);
    let params = Params {
        // Currently the circuit uses random access that only supports vectors of length 64.
        // With max_input_main_pods=3 we need random access to a vector of length 73.
        max_input_main_pods: 1,
        ..Default::default()
    };

    let processed_output = match lang::parse(&payload.code, &params) {
        Ok(output) => output,
        Err(e) => {
            log::error!("Failed to parse Podlog code: {:?}", e);
            return Err(PlaygroundApiError::Lang(e));
        }
    };

    let conn_check_space = match pool.get().await {
        Ok(conn) => conn,
        Err(e) => {
            log::error!("Failed to get DB connection for space check: {}", e);
            return Err(PlaygroundApiError::Internal(anyhow::anyhow!(
                "Failed to get DB connection: {}",
                e
            )));
        }
    };

    let space_id_check_clone = payload.space_id.clone();
    let space_exists: bool = match conn_check_space
        .interact(move |conn_inner| {
            conn_inner
                .query_row(
                    "SELECT 1 FROM spaces WHERE id = ?1",
                    [&space_id_check_clone],
                    |_| Ok(true),
                )
                .optional()
                .map(|opt| opt.is_some())
                .map_err(anyhow::Error::from)
        })
        .await
    {
        Ok(result) => match result {
            Ok(exists) => exists,
            Err(e) => {
                log::error!("Database error while checking space existence: {}", e);
                return Err(PlaygroundApiError::Internal(anyhow::anyhow!(
                    "Database error: {}",
                    e
                )));
            }
        },
        Err(e) => {
            log::error!(
                "Deadpool interact error while checking space existence: {}",
                e
            );
            return Err(PlaygroundApiError::Internal(anyhow::anyhow!(
                "Connection pool error: {}",
                e
            )));
        }
    };

    if !space_exists {
        log::warn!("Space '{}' not found for execution", payload.space_id);
        return Err(PlaygroundApiError::NotFound(format!(
            "Space with id '{}' not found for execution.",
            payload.space_id
        )));
    }

    let conn = match pool.get().await {
        Ok(conn) => conn,
        Err(e) => {
            log::error!("Failed to get DB connection for pod fetch: {}", e);
            return Err(PlaygroundApiError::Internal(anyhow::anyhow!(
                "Failed to get DB connection: {}",
                e
            )));
        }
    };
    let space_id_clone = payload.space_id.clone();

    let fetched_pod_infos = match conn
        .interact(move |conn_inner| {
            let mut stmt = conn_inner.prepare(
                "SELECT id, pod_type, data, label, created_at, space FROM pods WHERE space = ?1",
            )?;
            let pod_iter = stmt.query_map([&space_id_clone], |row| {
                let data_blob: Vec<u8> = row.get(2)?;
                let data_value: Value = serde_json::from_slice(&data_blob).map_err(|e| {
                    rusqlite::Error::FromSqlConversionFailure(
                        2,
                        rusqlite::types::Type::Blob,
                        Box::new(e),
                    )
                })?;
                Ok(PodInfo {
                    id: row.get(0)?,
                    pod_type: row.get(1)?,
                    data: serde_json::from_value(data_value).map_err(|e| {
                        rusqlite::Error::FromSqlConversionFailure(
                            2,
                            rusqlite::types::Type::Blob,
                            Box::new(e),
                        )
                    })?,
                    label: row.get(3)?,
                    created_at: row.get(4)?,
                    space: row.get(5)?,
                })
            })?;
            pod_iter.collect::<Result<Vec<_>, _>>()
        })
        .await
    {
        Ok(result) => match result {
            Ok(pods) => pods,
            Err(e) => {
                log::error!("Database error while fetching pods: {}", e);
                return Err(PlaygroundApiError::Internal(anyhow::anyhow!(
                    "Database error: {}",
                    e
                )));
            }
        },
        Err(e) => {
            log::error!("Deadpool interact error while fetching pods: {}", e);
            return Err(PlaygroundApiError::Internal(anyhow::anyhow!(
                "Connection pool error: {}",
                e
            )));
        }
    };

    if fetched_pod_infos.is_empty() {
        log::warn!(
            "No pods found in space '{}' for execution. Proceeding with empty facts.",
            payload.space_id
        );
    }

    let mut owned_signed_pods: Vec<SignedPod> = Vec::new();
    let mut owned_main_pods: Vec<MainPod> = Vec::new();

    for pod_info in fetched_pod_infos {
        // Sanity check: Ensure the pod_type string from DB matches the PodData enum variant type
        if pod_info.pod_type != pod_info.data.type_str() {
            log::warn!(
                "Data inconsistency for pod_id '{}' in space '{}' during execution: DB pod_type is '{}' but deserialized PodData is for '{}'. Trusting PodData enum.",
                pod_info.id, payload.space_id, pod_info.pod_type, pod_info.data.type_str()
            );
            // If they mismatch, we should probably trust the actual data content (the enum variant)
            // but it indicates a potential issue elsewhere (e.g., during import or manual DB edit).
        }

        match pod_info.data {
            PodData::Signed(helper) => {
                owned_signed_pods.push(SignedPod::from(helper));
            }
            PodData::Main(helper) => match MainPod::try_from(helper) {
                Ok(main_pod) => {
                    owned_main_pods.push(main_pod);
                }
                Err(e) => {
                    log::error!(
                        "Failed to convert MainPodHelper to MainPod (id: {}, space: {}): {:?}",
                        pod_info.id,
                        payload.space_id,
                        e
                    );
                    return Err(PlaygroundApiError::Internal(anyhow::anyhow!(
                        "Failed to process stored pod data for pod id {} in space {}: {:?}",
                        pod_info.id,
                        payload.space_id,
                        e
                    )));
                }
            },
        }
    }

    let mut all_pods_for_facts: Vec<&Box<dyn Pod>> = Vec::new();
    let mut original_signed_pods: HashMap<PodId, &SignedPod> = HashMap::new();
    let mut original_main_pods: HashMap<PodId, &MainPod> = HashMap::new();

    for signed_pod_ref in &owned_signed_pods {
        all_pods_for_facts.push(&signed_pod_ref.pod);
        original_signed_pods.insert(signed_pod_ref.id(), signed_pod_ref);
    }

    for main_pod_ref in &owned_main_pods {
        all_pods_for_facts.push(&main_pod_ref.pod);
        original_main_pods.insert(main_pod_ref.id(), main_pod_ref);
    }

    let initial_facts = facts_from_pods(&all_pods_for_facts);
    let custom_definitions =
        custom_definitions_from_batches(&[processed_output.custom_batch], &params);
    let request_templates = processed_output.request_templates;

    let solution = match solver::solve(
        &request_templates,
        &initial_facts,
        &params,
        &custom_definitions,
    ) {
        Ok(solution) => solution,
        Err(e) => {
            log::error!("Solver error: {:?}", e);
            return Err(PlaygroundApiError::Prover(e));
        }
    };

    let result_main_pod = match pod_building::build_main_pod_from_solution(
        &solution,
        &original_signed_pods,
        &original_main_pods,
        &params,
        &request_templates,
    ) {
        Ok(main_pod) => main_pod,
        Err(e) => {
            log::error!("Failed to build MainPod from solution: {:?}", e);
            return Err(PlaygroundApiError::Internal(anyhow::anyhow!(
                "Failed to build MainPod: {:?}",
                e
            )));
        }
    };

    let diagram = prover::visualization::generate_mermaid_markdown(&solution);

    let result = ExecuteResult {
        main_pod: result_main_pod,
        diagram,
    };

    Ok(Json(result))
}

#[derive(Debug)]
pub enum PlaygroundApiError {
    ValidationFailed(ValidateCodeResponse),
    Prover(ActualProverError),
    Lang(LangError),
    Internal(anyhow::Error),
    NotFound(String),
}

impl IntoResponse for PlaygroundApiError {
    fn into_response(self) -> axum::response::Response {
        match self {
            PlaygroundApiError::ValidationFailed(validation_response) => {
                log::warn!("Validation failed: {:?}", validation_response.diagnostics);
                (StatusCode::BAD_REQUEST, Json(validation_response)).into_response()
            }
            PlaygroundApiError::Prover(prover_error) => {
                log::error!("Prover error during execution: {:#?}", prover_error);
                let (status_code, error_message_str) = match prover_error {
                    ActualProverError::Unsatisfiable(_) => {
                        (StatusCode::BAD_REQUEST, "Proof request unsatisfiable")
                    }
                    _ => (StatusCode::INTERNAL_SERVER_ERROR, "Proof generation failed"),
                };
                let error_body = serde_json::json!({
                    "error": error_message_str,
                    "details": format!("{:?}", prover_error)
                });
                (status_code, Json(error_body)).into_response()
            }
            PlaygroundApiError::Lang(lang_error) => {
                log::error!("Language processing error: {:#?}", lang_error);
                let diagnostics = lang_error_to_diagnostics(&lang_error, "");
                let error_body = serde_json::json!({
                    "error": "Language processing error",
                    "diagnostics": diagnostics
                });
                (StatusCode::BAD_REQUEST, Json(error_body)).into_response()
            }
            PlaygroundApiError::Internal(err) => {
                log::error!("Internal server error: {:#}", err);
                let error_body = serde_json::json!({ "error": "Internal server error" });
                (StatusCode::INTERNAL_SERVER_ERROR, Json(error_body)).into_response()
            }
            PlaygroundApiError::NotFound(message) => {
                log::warn!("Playground API resource not found: {}", message);
                let error_body = serde_json::json!({
                    "error": "Not Found",
                    "message": message
                });
                (StatusCode::NOT_FOUND, Json(error_body)).into_response()
            }
        }
    }
}

impl From<LangError> for PlaygroundApiError {
    fn from(err: LangError) -> Self {
        PlaygroundApiError::Lang(err)
    }
}

impl From<ActualProverError> for PlaygroundApiError {
    fn from(err: ActualProverError) -> Self {
        PlaygroundApiError::Prover(err)
    }
}

impl From<anyhow::Error> for PlaygroundApiError {
    fn from(err: anyhow::Error) -> Self {
        PlaygroundApiError::Internal(err)
    }
}

pub async fn setup_zukyc_space(pool: &ConnectionPool) -> anyhow::Result<()> {
    let conn = match pool.get().await {
        Ok(c) => c,
        Err(e) => {
            log::error!("Failed to get DB connection for Zukyc space setup: {}", e);
            return Err(anyhow::anyhow!("Failed to get DB connection: {}", e)); // Early exit if no DB conn
        }
    };
    let space_id = "zukyc";

    // Check if space exists
    match conn
        .interact(move |conn_inner| {
            conn_inner
                .query_row(
                    "SELECT 1 FROM spaces WHERE id = ?1 LIMIT 1", // Ensure only one row is checked
                    params![&space_id],
                    |_| Ok(true), // If row exists, it's true
                )
                .optional() // Makes it Ok(None) if no rows, or Ok(Some(true))
        })
        .await
    {
        Ok(Ok(Some(true))) => {
            info!("Space '{}' already exists. Skipping setup.", space_id);
            return Ok(());
        }
        Ok(Ok(None)) => {
            info!(
                "Space '{}' does not exist. Proceeding with setup.",
                space_id
            );
        }
        Ok(Ok(Some(_))) => {
            // Catch any other Some(_) case, like an unexpected Some(false)
            log::warn!("Unexpected result while checking if space '{}' exists (e.g. Some(false)). Assuming it does not exist and proceeding with setup.", space_id);
        }
        Ok(Err(e)) => {
            log::error!(
                "DB error checking if space '{}' exists: {}. Proceeding with setup attempt anyway.",
                space_id,
                e
            );
        }
        Err(e) => {
            log::error!("Interaction error checking if space '{}' exists: {}. Proceeding with setup attempt anyway.", space_id, e);
        }
    }

    info!("Setting up space '{}' with Zukyc sample pods...", space_id);
    let now_str = Utc::now().to_rfc3339();
    let space_id_for_insert = space_id.to_string(); // Clone for closure
    if let Err(e) = conn
        .interact(move |conn_inner| {
            conn_inner.execute(
                "INSERT INTO spaces (id, created_at) VALUES (?1, ?2) ON CONFLICT(id) DO NOTHING",
                params![&space_id_for_insert, &now_str],
            )
        })
        .await
    {
        log::error!(
            "Interaction error while creating space '{}': {}",
            space_id,
            e
        );
        // Depending on desired strictness, could return Err here.
        // For now, we log and attempt to continue inserting pods.
    }

    let params_for_test = Params::default();
    let mut gov_signer = Signer(SecretKey(RawValue::from(1)));
    let mut pay_signer = Signer(SecretKey(RawValue::from(2)));
    let mut sanction_signer = Signer(SecretKey(RawValue::from(3)));

    let mut gov_id_builder = SignedPodBuilder::new(&params_for_test);
    gov_id_builder.insert("idNumber", "4242424242");
    gov_id_builder.insert("dateOfBirth", 1169909384);
    gov_id_builder.insert("socialSecurityNumber", "G2121210");

    match gov_id_builder.sign(&mut gov_signer) {
        Ok(gov_id_pod_signed) => {
            let gov_id_helper: SerializedSignedPod = gov_id_pod_signed.clone().into();
            let gov_pod_id_str: String = gov_id_pod_signed.id().encode_hex();
            let data_blob_gov = match serde_json::to_vec(&PodData::Signed(gov_id_helper.clone())) {
                Ok(blob) => blob,
                Err(e) => {
                    log::error!("Failed to serialize Gov ID pod data for Zukyc setup: {}", e);
                    return Ok(()); // Or continue to next pod
                }
            };
            let space_id_clone_gov = space_id.to_string();
            let conn_gov_op = pool.get().await;
            if let Ok(conn_gov) = conn_gov_op {
                if let Err(e) = conn_gov.interact(move |conn_inner| {
                    conn_inner.execute(
                        "INSERT INTO pods (id, pod_type, data, label, created_at, space) VALUES (?1, ?2, ?3, ?4, ?5, ?6) ON CONFLICT(space, id) DO NOTHING",
                        rusqlite::params![gov_pod_id_str, "signed", data_blob_gov, "Gov ID", Utc::now().to_rfc3339(), space_id_clone_gov],
                    )
                }).await {
                    log::error!("Failed to insert Gov ID pod into Zukyc space '{}': {}", space_id, e);
                }
            } else {
                log::error!(
                    "Failed to get DB connection for Gov ID pod insertion: {}",
                    conn_gov_op.unwrap_err()
                );
            }
        }
        Err(e) => {
            log::error!("Failed to sign Gov ID pod for Zukyc setup: {}", e);
        }
    }

    let mut pay_stub_builder = SignedPodBuilder::new(&params_for_test);
    pay_stub_builder.insert("socialSecurityNumber", "G2121210");
    pay_stub_builder.insert("startDate", 1706367566);
    match pay_stub_builder.sign(&mut pay_signer) {
        Ok(pay_stub_pod_signed) => {
            let pay_stub_helper: SerializedSignedPod = pay_stub_pod_signed.clone().into();
            let pay_pod_id_str: String = pay_stub_pod_signed.id().encode_hex();
            let data_blob_pay = match serde_json::to_vec(&PodData::Signed(pay_stub_helper.clone()))
            {
                Ok(blob) => blob,
                Err(e) => {
                    log::error!(
                        "Failed to serialize Pay Stub pod data for Zukyc setup: {}",
                        e
                    );
                    return Ok(()); // Or continue
                }
            };
            let space_id_clone_pay = space_id.to_string();
            let conn_pay_op = pool.get().await;
            if let Ok(conn_pay) = conn_pay_op {
                if let Err(e) = conn_pay.interact(move |conn_inner| {
                    conn_inner.execute(
                        "INSERT INTO pods (id, pod_type, data, label, created_at, space) VALUES (?1, ?2, ?3, ?4, ?5, ?6) ON CONFLICT(space, id) DO NOTHING",
                        rusqlite::params![pay_pod_id_str, "signed", data_blob_pay, "Pay Stub", Utc::now().to_rfc3339(), space_id_clone_pay],
                    )
                }).await {
                    log::error!("Failed to insert Pay Stub pod into Zukyc space '{}': {}", space_id, e);
                }
            } else {
                log::error!(
                    "Failed to get DB connection for Pay Stub pod insertion: {}",
                    conn_pay_op.unwrap_err()
                );
            }
        }
        Err(e) => {
            log::error!("Failed to sign Pay Stub pod for Zukyc setup: {}", e);
        }
    }

    let sanctions_values_set: HashSet<PodValue> =
        ["A343434340"].iter().map(|s| PodValue::from(*s)).collect();

    match Set::new(sanctions_values_set) {
        Ok(sanction_set_typed) => {
            let sanction_set_val = PodValue::from(sanction_set_typed);
            let mut sanction_list_builder = SignedPodBuilder::new(&params_for_test);
            sanction_list_builder.insert("sanctionList", sanction_set_val);
            match sanction_list_builder.sign(&mut sanction_signer) {
                Ok(sanction_list_pod_signed) => {
                    let sanction_list_helper: SerializedSignedPod =
                        sanction_list_pod_signed.clone().into();
                    let sanction_pod_id_str: String = sanction_list_pod_signed.id().encode_hex();
                    let data_blob_sanction =
                        match serde_json::to_vec(&PodData::Signed(sanction_list_helper.clone())) {
                            Ok(blob) => blob,
                            Err(e) => {
                                log::error!(
                                "Failed to serialize Sanctions List pod data for Zukyc setup: {}",
                                e
                            );
                                return Ok(()); // Or continue
                            }
                        };
                    let space_id_clone_sanction = space_id.to_string();
                    let conn_sanction_op = pool.get().await;
                    if let Ok(conn_sanction) = conn_sanction_op {
                        if let Err(e) = conn_sanction.interact(move |conn_inner| {
                            conn_inner.execute(
                                "INSERT INTO pods (id, pod_type, data, label, created_at, space) VALUES (?1, ?2, ?3, ?4, ?5, ?6) ON CONFLICT(space, id) DO NOTHING",
                                rusqlite::params![sanction_pod_id_str, "signed", data_blob_sanction, "Sanctions List", Utc::now().to_rfc3339(), space_id_clone_sanction],
                            )
                        }).await {
                            log::error!("Failed to insert Sanctions List pod into Zukyc space '{}': {}", space_id, e);
                        }
                    } else {
                        log::error!(
                            "Failed to get DB connection for Sanction List pod insertion: {}",
                            conn_sanction_op.unwrap_err()
                        );
                    }
                }
                Err(e) => {
                    log::error!("Failed to sign Sanctions List pod for Zukyc setup: {}", e);
                }
            }
        }
        Err(e) => {
            log::error!("Failed to create sanction set for Zukyc setup: {}", e);
        }
    }

    info!(
        "Zukyc space setup attempt complete for space '{}'. Check logs for any errors.",
        space_id
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::{io::Write, sync::Once};

    use axum_test::TestServer;
    use chrono::Utc;
    use env_logger::Builder;
    use serde_json::json;

    use super::*; // Imports handlers, PlaygroundApiError, etc.
    use crate::{
        backends::plonky2::mock::signedpod::MockSigner,
        server::{
            db::{self, init_db_pool, ConnectionPool},
            routes::create_router,
        },
    };

    static INIT: Once = Once::new();
    fn setup_test_logging() {
        INIT.call_once(|| {
            Builder::from_default_env()
                .format(|buf, record| {
                    writeln!(
                        buf,
                        "{} [{}] - {}",
                        chrono::Local::now().format("%Y-%m-%d %H:%M:%S"),
                        record.level(),
                        record.args()
                    )
                })
                .filter(None, log::LevelFilter::Debug)
                .init();
        });
    }

    async fn create_playground_server() -> TestServer {
        setup_test_logging();
        let pool = init_db_pool(None)
            .await
            .expect("Failed to init in-memory db pool for test");
        db::create_schema(&pool)
            .await
            .expect("Failed to create schema in create_playground_server");
        let router = create_router(pool.clone());
        TestServer::new(router).unwrap()
    }

    async fn create_playground_server_with_pool() -> (TestServer, ConnectionPool) {
        setup_test_logging();
        let pool = init_db_pool(None)
            .await
            .expect("Failed to init in-memory db pool for test");
        db::create_schema(&pool)
            .await
            .expect("Failed to create schema in create_playground_server_with_pool");
        let router = create_router(pool.clone());
        (TestServer::new(router).unwrap(), pool)
    }

    #[tokio::test]
    async fn test_execute_code_with_space_success() {
        let (server, pool) = create_playground_server_with_pool().await;
        let space_id = "exec-space-success-real";

        // Create the space directly in DB for test setup
        let space_id_clone_setup = space_id.to_string();
        let conn_setup = pool.get().await.unwrap();
        conn_setup
            .interact(move |conn_inner| {
                conn_inner.execute(
                    "INSERT INTO spaces (id, created_at) VALUES (?1, ?2)",
                    [&space_id_clone_setup, &Utc::now().to_rfc3339()],
                )
            })
            .await
            .unwrap()
            .unwrap();

        let params_for_test = Params::default();
        let mut gov_signer = MockSigner { pk: "gov".into() };
        let mut pay_signer = MockSigner { pk: "pay".into() };
        let mut sanction_signer = MockSigner {
            pk: "sanction".into(),
        };

        let mut gov_id_builder = SignedPodBuilder::new(&params_for_test);
        gov_id_builder.insert("idNumber", "4242424242");
        gov_id_builder.insert("dateOfBirth", 1169909384);
        gov_id_builder.insert("socialSecurityNumber", "G2121210");
        let gov_id_pod_signed = gov_id_builder.sign(&mut gov_signer).unwrap();
        let gov_id_helper: SerializedSignedPod = gov_id_pod_signed.clone().into();
        let gov_pod_id_str: String = gov_id_pod_signed.id().encode_hex();

        // Import pod directly into DB for test setup
        let data_blob_gov = serde_json::to_vec(&PodData::Signed(gov_id_helper.clone())).unwrap(); // Wrap helper in PodData
        let space_id_clone_gov = space_id.to_string();
        let conn_gov = pool.get().await.unwrap();
        conn_gov
            .interact(move |conn_inner| {
                conn_inner.execute(
                    "INSERT INTO pods (id, pod_type, data, label, created_at, space) VALUES (?1, ?2, ?3, ?4, ?5, ?6)",
                    rusqlite::params![gov_pod_id_str, "signed", data_blob_gov, "Gov ID", Utc::now().to_rfc3339(), space_id_clone_gov],
                )
            })
            .await
            .unwrap()
            .unwrap();

        let mut pay_stub_builder = SignedPodBuilder::new(&params_for_test);
        pay_stub_builder.insert("socialSecurityNumber", "G2121210");
        pay_stub_builder.insert("startDate", 1706367566);
        let pay_stub_pod_signed = pay_stub_builder.sign(&mut pay_signer).unwrap();
        let pay_stub_helper: SerializedSignedPod = pay_stub_pod_signed.clone().into();
        let pay_pod_id_str: String = pay_stub_pod_signed.id().encode_hex();

        let data_blob_pay = serde_json::to_vec(&PodData::Signed(pay_stub_helper.clone())).unwrap(); // Wrap helper in PodData
        let space_id_clone_pay = space_id.to_string();
        let conn_pay = pool.get().await.unwrap();
        conn_pay
            .interact(move |conn_inner| {
                conn_inner.execute(
                    "INSERT INTO pods (id, pod_type, data, label, created_at, space) VALUES (?1, ?2, ?3, ?4, ?5, ?6)",
                    rusqlite::params![pay_pod_id_str, "signed", data_blob_pay, "Pay Stub", Utc::now().to_rfc3339(), space_id_clone_pay],
                )
            })
            .await
            .unwrap()
            .unwrap();

        let sanctions_values_set: HashSet<PodValue> =
            ["A343434340"].iter().map(|s| PodValue::from(*s)).collect();
        let sanction_set_val = PodValue::from(Set::new(sanctions_values_set).unwrap());
        let mut sanction_list_builder = SignedPodBuilder::new(&params_for_test);
        sanction_list_builder.insert("sanctionList", sanction_set_val);
        let sanction_list_pod_signed = sanction_list_builder.sign(&mut sanction_signer).unwrap();
        let sanction_list_helper: SerializedSignedPod = sanction_list_pod_signed.clone().into();
        let sanction_pod_id_str: String = sanction_list_pod_signed.id().encode_hex();

        let data_blob_sanction =
            serde_json::to_vec(&PodData::Signed(sanction_list_helper.clone())).unwrap(); // Wrap helper in PodData
        let space_id_clone_sanction = space_id.to_string();
        let conn_sanction = pool.get().await.unwrap();
        conn_sanction
            .interact(move |conn_inner| {
                conn_inner.execute(
                    "INSERT INTO pods (id, pod_type, data, label, created_at, space) VALUES (?1, ?2, ?3, ?4, ?5, ?6)",
                    rusqlite::params![sanction_pod_id_str, "signed", data_blob_sanction, "Sanctions List", Utc::now().to_rfc3339(), space_id_clone_sanction],
                )
            })
            .await
            .unwrap()
            .unwrap();

        let valid_zukyc_podlog = r#"
        REQUEST(
            NotContains(?sanctions["sanctionList"], ?gov["idNumber"])
            Lt(?gov["dateOfBirth"], ?SELF_HOLDER_18Y["const_18y"])
            Equal(?pay["startDate"], ?SELF_HOLDER_1Y["const_1y"])
            Equal(?gov["socialSecurityNumber"], ?pay["socialSecurityNumber"])
            ValueOf(?SELF_HOLDER_18Y["const_18y"], 1169909388)
            ValueOf(?SELF_HOLDER_1Y["const_1y"], 1706367566)
        )
        "#;

        let request_payload = json!({
            "code": valid_zukyc_podlog,
            "space_id": space_id
        });

        let response = server.post("/api/execute").json(&request_payload).await;
        assert_eq!(
            response.status_code(),
            StatusCode::OK,
            "Response body: {:?}",
            response.text()
        );
        let main_pod_result: MainPod = response.json();
        assert_eq!(
            main_pod_result.public_statements.len(),
            7,
            "Expected 7 public statements (6 requests + 1 _type)"
        );
    }

    #[tokio::test]
    async fn test_validate_code_valid_code() {
        let server = create_playground_server().await;

        let valid_podlog_code = r#"
        is_older(PersonA, PersonB) = AND(
            Gt(?PersonA["age"], ?PersonB["age"])
        )
        REQUEST(
            is_older(?Alice, ?Bob)
        )
        "#;

        let request_payload = json!({
            "code": valid_podlog_code
        });

        let response = server.post("/api/validate").json(&request_payload).await;

        assert_eq!(response.status_code(), StatusCode::OK);
        let response_json: serde_json::Value = response.json();

        let diagnostics = response_json
            .get("diagnostics")
            .expect("Response should have a 'diagnostics' field");
        assert!(
            diagnostics.is_array(),
            "'diagnostics' field should be an array"
        );
        assert!(
            diagnostics.as_array().unwrap().is_empty(),
            "Expected no diagnostics for valid code, got: {:?}",
            diagnostics
        );
    }

    #[tokio::test]
    async fn test_validate_code_parsing_error() {
        let server = create_playground_server().await;

        let invalid_podlog_code = r#"REQEST("#;

        let request_payload = json!({
            "code": invalid_podlog_code
        });

        let response = server.post("/api/validate").json(&request_payload).await;

        assert_eq!(response.status_code(), StatusCode::OK);
        let response_json: serde_json::Value = response.json();

        let diagnostics_val = response_json
            .get("diagnostics")
            .expect("Response should have a 'diagnostics' field");
        assert!(
            diagnostics_val.is_array(),
            "'diagnostics' field should be an array"
        );
        let diagnostics_array = diagnostics_val.as_array().unwrap();

        assert!(
            !diagnostics_array.is_empty(),
            "Expected diagnostics for invalid code, but got none."
        );
        assert_eq!(
            diagnostics_array.len(),
            1,
            "Expected one diagnostic for this specific parse error, got: {:?}",
            diagnostics_array
        );

        let diagnostic_one = &diagnostics_array[0];
        let message = diagnostic_one.get("message").unwrap().as_str().unwrap();

        assert!(message.to_lowercase().contains("expected"), 
                "Diagnostic message '{}' did not contain 'expected'. Actual pest error might be more specific.", message);

        assert_eq!(
            diagnostic_one.get("severity").unwrap().as_str().unwrap(),
            "Error"
        );

        let start_line = diagnostic_one.get("start_line").unwrap().as_u64().unwrap();
        let start_col = diagnostic_one
            .get("start_column")
            .unwrap()
            .as_u64()
            .unwrap();
        assert_eq!(start_line, 1);
        assert_eq!(start_col, 8);
    }

    #[tokio::test]
    async fn test_execute_mvp_zukyc_success() {
        let server = create_playground_server().await;

        let valid_zukyc_podlog = r#"
        REQUEST(
            NotContains(?sanctions["sanctionList"], ?gov["idNumber"])
            Lt(?gov["dateOfBirth"], ?SELF_HOLDER_18Y["const_18y"])
            Equal(?pay["startDate"], ?SELF_HOLDER_1Y["const_1y"])
            Equal(?gov["socialSecurityNumber"], ?pay["socialSecurityNumber"])
            ValueOf(?SELF_HOLDER_18Y["const_18y"], 1169909388)
            ValueOf(?SELF_HOLDER_1Y["const_1y"], 1706367566)
        )
        "#;

        let request_payload = json!({
            "code": valid_zukyc_podlog
        });

        let response = server.post("/api/executeMvp").json(&request_payload).await;

        assert_eq!(
            response.status_code(),
            StatusCode::OK,
            "Response body: {:?}",
            response.text()
        );

        let response_json: serde_json::Value = response.json();
        assert!(response_json.is_object());
        assert!(response_json.get("publicStatements").is_some());
        assert!(response_json.get("publicStatements").unwrap().is_array());
        assert_eq!(
            response_json
                .get("publicStatements")
                .unwrap()
                .as_array()
                .unwrap()
                .len(),
            7
        );
    }

    #[tokio::test]
    async fn test_execute_mvp_parsing_error() {
        let server = create_playground_server().await;
        let invalid_podlog_code = r#"REQEST("#;

        let request_payload = json!({
            "code": invalid_podlog_code
        });

        let response = server.post("/api/executeMvp").json(&request_payload).await;

        assert_eq!(
            response.status_code(),
            StatusCode::BAD_REQUEST,
            "Response body: {:?}",
            response.text()
        );
        let response_json: serde_json::Value = response.json();
        assert_eq!(
            response_json.get("error").unwrap().as_str().unwrap(),
            "Language processing error"
        );
        assert!(response_json.get("diagnostics").unwrap().is_array());
        assert!(!response_json
            .get("diagnostics")
            .unwrap()
            .as_array()
            .unwrap()
            .is_empty());
    }

    #[tokio::test]
    async fn test_execute_mvp_unsatisfiable_proof() {
        let server = create_playground_server().await;

        let unsatisfiable_podlog = r#"
        REQUEST(
            Equal(?gov["idNumber"], ?gov["a_non_existent_key"]) 
        )
        "#;

        let request_payload = json!({
            "code": unsatisfiable_podlog
        });

        let response = server.post("/api/executeMvp").json(&request_payload).await;

        assert_eq!(
            response.status_code(),
            StatusCode::BAD_REQUEST,
            "Response body: {:?}",
            response.text()
        );
        let response_json: serde_json::Value = response.json();
        assert_eq!(
            response_json.get("error").unwrap().as_str().unwrap(),
            "Proof request unsatisfiable"
        );
        assert!(response_json
            .get("details")
            .unwrap()
            .as_str()
            .unwrap()
            .starts_with("Unsatisfiable"));
    }

    #[tokio::test]
    async fn test_execute_code_with_space_not_found() {
        let server = create_playground_server().await;
        let space_id = "non-existent-exec-space-for-playground";

        // Ensure the space does NOT exist for this test case.
        // If space is not found, execute_code_handler should return PlaygroundApiError::NotFound.

        let podlog_code = r#"REQUEST(Equal(?gov["idNumber"], ?gov["idNumber"]))"#;

        let request_payload = json!({
            "code": podlog_code,
            "space_id": space_id
        });

        let response = server.post("/api/execute").json(&request_payload).await;
        assert_eq!(
            response.status_code(),
            StatusCode::NOT_FOUND,
            "Response body: {:?}",
            response.text()
        );
        let response_json: serde_json::Value = response.json();
        assert_eq!(
            response_json.get("error").unwrap().as_str().unwrap(),
            "Not Found"
        );
        assert!(response_json
            .get("message")
            .unwrap()
            .as_str()
            .unwrap()
            .contains(&format!(
                "Space with id '{}' not found for execution.",
                space_id
            )));
    }
}
