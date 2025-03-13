// Web module for POD2 Web Viewer
// Contains API handlers and storage utilities

use actix_web::{web, HttpResponse, Responder};
use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use uuid::Uuid;

use crate::frontend::{SignedPod, SignedPodBuilder, Value};
use crate::middleware::{Params, PodSigner, KEY_SIGNER, KEY_TYPE};
use crate::backends::plonky2::mock_signed::MockSigner;

// Type alias for our in-memory storage
pub type PodStorage = Arc<RwLock<HashMap<String, SignedPod>>>;

// API Models
#[derive(Debug, Serialize, Deserialize)]
pub struct PodListResponse {
    pub pods: Vec<PodInfo>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct PodInfo {
    pub id: String,
    pub pod_class: String,
    pub signer: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct PodDetailResponse {
    pub id: String,
    pub pod_class: String,
    pub signer: String, 
    pub entries: HashMap<String, Value>,
    pub created_at: chrono::DateTime<chrono::Utc>,
    pub is_valid: bool,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct CreateSignedPodRequest {
    pub entries: HashMap<String, serde_json::Value>,
    pub signer: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct ImportPodRequest {
    pub pod_data: String, // JSON serialized pod
}

// Helper to convert JSON values to POD values
fn json_to_pod_value(value: &serde_json::Value) -> Result<Value> {
    match value {
        serde_json::Value::String(s) => Ok(Value::String(s.clone())),
        serde_json::Value::Number(n) => {
            if let Some(i) = n.as_i64() {
                Ok(Value::Int(i))
            } else {
                anyhow::bail!("Number not representable as i64")
            }
        },
        serde_json::Value::Bool(b) => Ok(Value::Bool(*b)),
        serde_json::Value::Array(_) => {
            anyhow::bail!("Array values not implemented yet")
        },
        serde_json::Value::Object(_) => {
            anyhow::bail!("Object values not implemented yet")
        },
        serde_json::Value::Null => {
            anyhow::bail!("Null values not supported")
        },
    }
}

// API Handlers
pub async fn get_pods(storage: web::Data<PodStorage>) -> impl Responder {
    let storage = storage.read().unwrap();
    
    let pods: Vec<PodInfo> = storage
        .iter()
        .map(|(id, pod)| {
            // Get signer from pod
            let signer = pod.kvs.get(KEY_SIGNER)
                .map(|v| v.to_string())
                .unwrap_or_else(|| "Unknown".to_string());
            
            PodInfo {
                id: id.clone(),
                pod_class: "Signed".to_string(), // Currently only handling SignedPods
                signer,
                created_at: chrono::Utc::now(), // We don't store creation time yet
            }
        })
        .collect();
    
    HttpResponse::Ok().json(PodListResponse { pods })
}

pub async fn get_pod_by_id(
    id: web::Path<String>,
    storage: web::Data<PodStorage>
) -> impl Responder {
    let storage = storage.read().unwrap();
    
    match storage.get(id.as_str()) {
        Some(pod) => {
            // Get signer from pod
            let signer = pod.kvs.get(KEY_SIGNER)
                .map(|v| v.to_string())
                .unwrap_or_else(|| "Unknown".to_string());
            
            let response = PodDetailResponse {
                id: id.to_string(),
                pod_class: "Signed".to_string(),
                signer,
                entries: pod.kvs.clone(),
                created_at: chrono::Utc::now(), // We don't store creation time yet
                is_valid: pod.verify(),
            };
            
            HttpResponse::Ok().json(response)
        },
        None => HttpResponse::NotFound().json(serde_json::json!({
            "error": "Pod not found"
        }))
    }
}

pub async fn create_signed_pod(
    req: web::Json<CreateSignedPodRequest>,
    storage: web::Data<PodStorage>
) -> impl Responder {
    // Convert entries to POD values
    let mut pod_entries = HashMap::new();
    for (key, value) in &req.entries {
        match json_to_pod_value(value) {
            Ok(pod_value) => {
                pod_entries.insert(key.clone(), pod_value);
            },
            Err(e) => {
                return HttpResponse::BadRequest().json(serde_json::json!({
                    "error": format!("Failed to convert value for key '{}': {}", key, e)
                }));
            }
        }
    }
    
    // Create and sign the pod
    let params = Params::default();
    let mut builder = SignedPodBuilder::new(&params);
    
    // Add entries to the pod
    for (key, value) in pod_entries {
        builder.insert(key, value);
    }
    
    // Create a mock signer with the requested key
    let mut signer = MockSigner { pk: req.signer.clone() };
    
    // Sign the pod
    match builder.sign(&mut signer) {
        Ok(pod) => {
            // Generate a UUID for the pod
            let pod_id = Uuid::new_v4().to_string();
            
            // Store the pod
            let mut storage = storage.write().unwrap();
            storage.insert(pod_id.clone(), pod.clone());
            
            // Return the pod ID
            HttpResponse::Created().json(serde_json::json!({
                "id": pod_id,
                "message": "Pod created successfully"
            }))
        },
        Err(e) => {
            HttpResponse::InternalServerError().json(serde_json::json!({
                "error": format!("Failed to sign pod: {}", e)
            }))
        }
    }
}

pub async fn import_pod(
    req: web::Json<ImportPodRequest>,
    storage: web::Data<PodStorage>
) -> impl Responder {
    // Deserialize the pod
    match serde_json::from_str::<SignedPod>(&req.pod_data) {
        Ok(pod) => {
            // Generate a UUID for the pod
            let pod_id = Uuid::new_v4().to_string();
            
            // Store the pod
            let mut storage = storage.write().unwrap();
            storage.insert(pod_id.clone(), pod);
            
            // Return the pod ID
            HttpResponse::Created().json(serde_json::json!({
                "id": pod_id,
                "message": "Pod imported successfully"
            }))
        },
        Err(e) => {
            HttpResponse::BadRequest().json(serde_json::json!({
                "error": format!("Failed to deserialize pod: {}", e)
            }))
        }
    }
}

pub async fn export_pod(
    id: web::Path<String>,
    storage: web::Data<PodStorage>
) -> impl Responder {
    let storage = storage.read().unwrap();
    
    match storage.get(id.as_str()) {
        Some(pod) => {
            // Serialize the pod to JSON
            match serde_json::to_string(&pod) {
                Ok(pod_json) => {
                    HttpResponse::Ok().json(serde_json::json!({
                        "pod_data": pod_json
                    }))
                },
                Err(e) => {
                    HttpResponse::InternalServerError().json(serde_json::json!({
                        "error": format!("Failed to serialize pod: {}", e)
                    }))
                }
            }
        },
        None => HttpResponse::NotFound().json(serde_json::json!({
            "error": "Pod not found"
        }))
    }
}