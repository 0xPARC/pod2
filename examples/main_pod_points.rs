#![allow(clippy::uninlined_format_args)] // TODO: Remove this in another PR
//! Example of building main pods that verify signed pods and other main pods using custom
//! predicates
//!
//! The example follows a scenario where a game issues signed pods to players with the points
//! accumulated after finishing each game level.  Then we build a custom predicate to prove that
//! the sum of points from level 1 and 2 for a player is over 9000.
//!
//! Run in real mode: `cargo run --release --example main_pod_points`
//! Run in mock mode: `cargo run --release --example main_pod_points -- --mock`
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
        (&VDSet::new(8, &[])?, &mock_prover)
    } else {
        println!("Prebuilding circuits to calculate vd_set...");
        let vd_set = &*DEFAULT_VD_SET;
        println!("vd_set calculation complete");
        (vd_set, &real_prover)
    };

    // Create a schnorr key pair to sign pods
    let game_sk = SecretKey::new_rand();
    let game_pk = game_sk.public_key();

    let game_signer = Signer(game_sk);

    // Build 2 signed pods where the game assigns points to a player that has completed a level.
    let mut builder = SignedDictBuilder::new(&params);
    builder.insert("player", "Alice");
    builder.insert("level", 1);
    builder.insert("points", 3512);
    let pod_points_lvl_1 = builder.sign(&game_signer)?;
    pod_points_lvl_1.verify()?;
    println!("# pod_points_lvl_1:\n{}", pod_points_lvl_1);

    let mut builder = SignedDictBuilder::new(&params);
    builder.insert("player", "Alice");
    builder.insert("level", 2);
    builder.insert("points", 5771);
    let pod_points_lvl_2 = builder.sign(&game_signer)?;
    pod_points_lvl_2.verify()?;
    println!("# pod_points_lvl_2:\n{}", pod_points_lvl_2);

    // Build a MainPod to prove >9000 points from sum of level 1 and 2

    // Declare the custom predicate
    let input = format!(
        r#"
        points(player, level, points, private: points_dict) = AND(
            SignedBy(points_dict, PublicKey({game_pk}))
            Contains(points_dict, "player", player)
            Contains(points_dict, "level", level)
            Contains(points_dict, "points", points)
        )

        over_9000(player, private: points_lvl_1, points_lvl_2, points_total) = AND(
            points(player, 1, points_lvl_1)
            points(player, 2, points_lvl_2)
            SumOf(points_total, points_lvl_1, points_lvl_2)
            Gt(points_total, 9000)
        )
    "#,
        game_pk = game_pk,
    );
    println!("# custom predicate batch:{}", input);
    let batch = parse(&input, &params, &[])?.custom_batch;
    let points_pred = batch.predicate_ref_by_name("points").unwrap();
    let over_9000_pred = batch.predicate_ref_by_name("over_9000").unwrap();

    // Build a pod to prove the statement `points("Alice", 1, 3512)`
    let mut builder = MainPodBuilder::new(&params, vd_set);
    let st_signed_by = builder.priv_op(Operation::dict_signed_by(&pod_points_lvl_1))?;
    let st_player = builder.priv_op(Operation::dict_contains(
        pod_points_lvl_1.dict.clone(),
        "player",
        "Alice",
    ))?;
    let st_level = builder.priv_op(Operation::dict_contains(
        pod_points_lvl_1.dict.clone(),
        "level",
        1,
    ))?;
    let st_points = builder.priv_op(Operation::dict_contains(
        pod_points_lvl_1.dict.clone(),
        "points",
        3512,
    ))?;
    let st_points_lvl_1 = builder.pub_op(Operation::custom(
        points_pred.clone(),
        [st_signed_by, st_player, st_level, st_points],
    ))?;

    let pod_alice_lvl_1_points = builder.prove(prover).unwrap();
    println!("# pod_alice_lvl_1_points\n:{}", pod_alice_lvl_1_points);
    pod_alice_lvl_1_points.pod.verify().unwrap();

    // Build a pod to prove the statement `points("Alice", 2, 5771)`
    let mut builder = MainPodBuilder::new(&params, vd_set);
    let st_signed_by = builder.priv_op(Operation::dict_signed_by(&pod_points_lvl_2))?;
    let st_player = builder.priv_op(Operation::dict_contains(
        pod_points_lvl_2.dict.clone(),
        "player",
        "Alice",
    ))?;
    let st_level = builder.priv_op(Operation::dict_contains(
        pod_points_lvl_2.dict.clone(),
        "level",
        2,
    ))?;
    let st_points = builder.priv_op(Operation::dict_contains(
        pod_points_lvl_2.dict.clone(),
        "points",
        5771,
    ))?;

    let st_points_lvl_2 = builder.pub_op(Operation::custom(
        points_pred,
        [st_signed_by, st_player, st_level, st_points],
    ))?;
    let pod_alice_lvl_2_points = builder.prove(prover).unwrap();
    println!("# pod_alice_lvl_2_points\n:{}", pod_alice_lvl_2_points);
    pod_alice_lvl_2_points.pod.verify().unwrap();

    // Build a pod to prove the statement `over_9000("Alice")`
    let mut builder = MainPodBuilder::new(&params, vd_set);
    builder.add_pod(pod_alice_lvl_1_points);
    builder.add_pod(pod_alice_lvl_2_points);
    let st_points_total = builder.priv_op(Operation::sum_of(3512 + 5771, 3512, 5771))?;
    let st_gt_9000 = builder.priv_op(Operation::gt(3512 + 5771, 9000))?;
    let _st_over_9000 = builder.pub_op(Operation::custom(
        over_9000_pred,
        [
            st_points_lvl_1,
            st_points_lvl_2,
            st_points_total,
            st_gt_9000,
        ],
    ));
    let pod_alice_over_9000 = builder.prove(prover).unwrap();
    println!("# pod_alice_over_9000\n:{}", pod_alice_over_9000);
    pod_alice_over_9000.pod.verify().unwrap();

    Ok(())
}
