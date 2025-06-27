use std::collections::HashSet;

use chrono::Utc;
use hex::ToHex;
use log::info;
use num::BigUint;
use rusqlite::{params, OptionalExtension};

use crate::{
    backends::plonky2::{primitives::ec::schnorr::SecretKey, signedpod::Signer},
    frontend::{serialization::SerializedSignedPod, SignedPodBuilder},
    middleware::{containers::Set, Params, Value as PodValue},
    server::{db::ConnectionPool, handlers::pod_management::PodData},
};

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
    let mut gov_signer = Signer(SecretKey(BigUint::from(1u32)));
    let mut pay_signer = Signer(SecretKey(BigUint::from(2u32)));
    let mut sanction_signer = Signer(SecretKey(BigUint::from(3u32)));

    let mut gov_id_builder = SignedPodBuilder::new(&params_for_test);
    gov_id_builder.insert("idNumber", "4242424242");
    gov_id_builder.insert("dateOfBirth", 1169909384);
    gov_id_builder.insert("socialSecurityNumber", "G2121210");

    match gov_id_builder.sign(&mut gov_signer) {
        Ok(gov_id_pod_signed) => {
            let gov_id_helper: SerializedSignedPod = gov_id_pod_signed.clone().into();
            let gov_pod_id_str: String = gov_id_pod_signed.id().0.encode_hex();
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
            let pay_pod_id_str: String = pay_stub_pod_signed.id().0.encode_hex();
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

    match Set::new(
        params_for_test.max_depth_mt_containers,
        sanctions_values_set,
    ) {
        Ok(sanction_set_typed) => {
            let sanction_set_val = PodValue::from(sanction_set_typed);
            let mut sanction_list_builder = SignedPodBuilder::new(&params_for_test);
            sanction_list_builder.insert("sanctionList", sanction_set_val);
            match sanction_list_builder.sign(&mut sanction_signer) {
                Ok(sanction_list_pod_signed) => {
                    let sanction_list_helper: SerializedSignedPod =
                        sanction_list_pod_signed.clone().into();
                    let sanction_pod_id_str: String = sanction_list_pod_signed.id().0.encode_hex();
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
