#![allow(clippy::uninlined_format_args)]
//! Example of using the Abs operation with custom predicates
//!
//! This example models a bank account that issues signed pods with balance changes.
//! We then prove that the absolute value of a balance change is within acceptable limits,
//! without revealing whether it was a deposit or withdrawal.
//!
//! Run in real mode: `cargo run --release --example main_pod_balance_abs`
//! Run in mock mode: `cargo run --release --example main_pod_balance_abs -- --mock`
use std::env;

use pod2::{
    backends::plonky2::{
        basetypes::DEFAULT_VD_SET, mainpod::Prover, mock::mainpod::MockProver,
        primitives::ec::schnorr::SecretKey, signer::Signer,
    },
    frontend::{MainPodBuilder, Operation, SignedDictBuilder},
    lang::parse,
    middleware::{MainPodProver, Params, VDSet},
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();
    let args: Vec<String> = env::args().collect();
    let mock = args.get(1).is_some_and(|arg1| arg1 == "--mock");
    if mock {
        println!("Using MockMainPod")
    } else {
        println!("Using MainPod")
    }

    let params = Params::default();

    let mock_prover = MockProver {};
    let real_prover = Prover {};
    let (vd_set, prover): (_, &dyn MainPodProver) = if mock {
        (&VDSet::new(&[]), &mock_prover)
    } else {
        println!("Prebuilding circuits to calculate vd_set...");
        let vd_set = &*DEFAULT_VD_SET;
        println!("vd_set calculation complete");
        (vd_set, &real_prover)
    };

    // Create a schnorr key pair for the bank
    let bank_sk = SecretKey::new_rand();
    let bank_pk = bank_sk.public_key();

    let bank_signer = Signer(bank_sk);

    // Build a signed pod with a balance change (negative means withdrawal)
    let mut builder = SignedDictBuilder::new(&params);
    builder.insert("account", "ACC-12345");
    builder.insert("change", -75); // Withdrawal of $75
    let pod_balance_change = builder.sign(&bank_signer)?;
    pod_balance_change.verify()?;
    println!("# pod_balance_change:\n{}", pod_balance_change);

    // Declare custom predicates
    let input = format!(
        r#"
        balance_change(account, change, private: change_dict) = AND(
            SignedBy(change_dict, PublicKey({bank_pk}))
            Contains(change_dict, "account", account)
            Contains(change_dict, "change", change)
        )

        small_transaction(account, private: change, magnitude) = AND(
            balance_change(account, change)
            Abs(magnitude, change)
            Lt(magnitude, 100)
        )
    "#,
        bank_pk = bank_pk,
    );
    println!("# custom predicate batch:{}", input);
    let batch = parse(&input, &params, &[])?.custom_batch;
    let balance_change_pred = batch.predicate_ref_by_name("balance_change").unwrap();
    let small_transaction_pred = batch.predicate_ref_by_name("small_transaction").unwrap();

    // Build a pod to prove `balance_change("ACC-12345", -75)`
    let mut builder = MainPodBuilder::new(&params, vd_set);
    let st_signed_by = builder.priv_op(Operation::dict_signed_by(&pod_balance_change))?;
    let st_account = builder.priv_op(Operation::dict_contains(
        pod_balance_change.dict.clone(),
        "account",
        "ACC-12345",
    ))?;
    let st_change = builder.priv_op(Operation::dict_contains(
        pod_balance_change.dict.clone(),
        "change",
        -75,
    ))?;
    let st_balance_change = builder.pub_op(Operation::custom(
        balance_change_pred,
        [st_signed_by, st_account, st_change],
    ))?;

    let pod_change = builder.prove(prover)?;
    println!("# pod_change:\n{}", pod_change);
    pod_change.pod.verify()?;

    // Build a pod to prove `small_transaction("ACC-12345")`
    // This proves |change| < 100 without revealing if it was deposit or withdrawal
    let mut builder = MainPodBuilder::new(&params, vd_set);
    builder.add_pod(pod_change)?;

    // Calculate magnitude: abs(-75) = 75
    let st_magnitude = builder.priv_op(Operation::abs(75, -75))?;
    // Prove magnitude < 100
    let st_lt_100 = builder.priv_op(Operation::lt(75, 100))?;

    let _st_small = builder.pub_op(Operation::custom(
        small_transaction_pred,
        [st_balance_change, st_magnitude, st_lt_100],
    ))?;

    let pod_small_transaction = builder.prove(prover)?;
    println!("# pod_small_transaction:\n{}", pod_small_transaction);
    pod_small_transaction.pod.verify()?;

    println!("\n✓ Successfully proved transaction magnitude < $100 without revealing direction!");

    Ok(())
}
