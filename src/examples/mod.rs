pub mod custom;

use std::{collections::HashSet, sync::LazyLock};

use custom::eth_dos_batch;
use num::BigUint;

pub static MOCK_VD_SET: LazyLock<VDSet> = LazyLock::new(|| VDSet::new(6, &[]).unwrap());

use crate::{
    backends::plonky2::{primitives::ec::schnorr::SecretKey, signedpod::Signer},
    frontend::{
        MainPod, MainPodBuilder, Operation, PodRequest, Result, SignedPod, SignedPodBuilder,
    },
    lang::parse,
    middleware::{
        containers::Set, hash_values, CustomPredicateRef, Params, PodSigner, PodType, Predicate,
        Statement, StatementArg, TypedValue, VDSet, Value, KEY_SIGNER, KEY_TYPE,
    },
};

// ZuKYC

pub fn zu_kyc_sign_pod_builders(params: &Params) -> (SignedPodBuilder, SignedPodBuilder) {
    let mut gov_id = SignedPodBuilder::new(params);
    gov_id.insert("idNumber", "4242424242");
    gov_id.insert("dateOfBirth", 1169909384);
    gov_id.insert("socialSecurityNumber", "G2121210");

    let mut pay_stub = SignedPodBuilder::new(params);
    pay_stub.insert("socialSecurityNumber", "G2121210");
    pay_stub.insert("startDate", 1706367566);

    (gov_id, pay_stub)
}

pub const ZU_KYC_NOW_MINUS_18Y: i64 = 1169909388;
pub const ZU_KYC_NOW_MINUS_1Y: i64 = 1706367566;
pub const ZU_KYC_SANCTION_LIST: &[&str] = &["A343434340"];

pub fn zu_kyc_pod_builder(
    params: &Params,
    vd_set: &VDSet,
    gov_id: &SignedPod,
    pay_stub: &SignedPod,
) -> Result<MainPodBuilder> {
    let now_minus_18y = ZU_KYC_NOW_MINUS_18Y;
    let now_minus_1y = ZU_KYC_NOW_MINUS_1Y;
    let sanctions_values: HashSet<Value> = ZU_KYC_SANCTION_LIST
        .iter()
        .map(|s| Value::from(*s))
        .collect();
    let sanction_set =
        Value::from(Set::new(params.max_depth_mt_containers, sanctions_values).unwrap());

    let mut kyc = MainPodBuilder::new(params, vd_set);
    kyc.add_signed_pod(gov_id);
    kyc.add_signed_pod(pay_stub);
    kyc.pub_op(Operation::set_not_contains(
        sanction_set,
        (gov_id, "idNumber"),
    ))?;
    kyc.pub_op(Operation::lt((gov_id, "dateOfBirth"), now_minus_18y))?;
    kyc.pub_op(Operation::eq(
        (gov_id, "socialSecurityNumber"),
        (pay_stub, "socialSecurityNumber"),
    ))?;
    kyc.pub_op(Operation::eq((pay_stub, "startDate"), now_minus_1y))?;
    kyc.pub_op(Operation::eq(
        (gov_id, "_signer"),
        gov_id.get("_signer").unwrap(),
    ))?;
    kyc.pub_op(Operation::eq(
        (pay_stub, "_signer"),
        pay_stub.get("_signer").unwrap(),
    ))?;

    Ok(kyc)
}

pub fn zu_kyc_pod_request(gov_signer: &Value, pay_signer: &Value) -> Result<PodRequest> {
    let params = Params::default();
    let sanctions_values: HashSet<Value> = ZU_KYC_SANCTION_LIST
        .iter()
        .map(|s| Value::from(*s))
        .collect();
    let sanction_set =
        Value::from(Set::new(params.max_depth_mt_containers, sanctions_values).unwrap());
    let input = format!(
        r#"
    REQUEST(
        SetNotContains({sanction_set}, ?gov["idNumber"])
        Lt(?gov["dateOfBirth"], {ZU_KYC_NOW_MINUS_18Y})
        Equal(?pay["startDate"], {ZU_KYC_NOW_MINUS_1Y})
        Equal(?gov["socialSecurityNumber"], ?pay["socialSecurityNumber"])
        Equal(?gov["_signer"], {gov_signer})
        Equal(?pay["_signer"], {pay_signer})
        // TODO: Ownership check and watermarking
        // Depends partly on https://github.com/0xPARC/pod2/issues/351
    )
    "#,
    );
    let parsed = parse(&input, &Params::default(), &[])?;
    Ok(parsed.request)
}

// ETHDoS

pub fn attest_eth_friend(params: &Params, src: &impl PodSigner, dst: Value) -> SignedPod {
    let mut attestation = SignedPodBuilder::new(params);
    attestation.insert("attestation", dst);
    attestation.sign(src).unwrap()
}

pub struct EthDosHelper {
    params: Params,
    vd_set: VDSet,
    mock: bool,
    eth_friend: CustomPredicateRef,
    eth_dos_base: CustomPredicateRef,
    eth_dos_ind: CustomPredicateRef,
    eth_dos: CustomPredicateRef,
    src: Value,
}

impl EthDosHelper {
    pub fn new(params: &Params, vd_set: &VDSet, mock: bool, src: Value) -> Result<Self> {
        let eth_dos_batch = eth_dos_batch(params)?;
        let eth_friend = eth_dos_batch.predicate_ref_by_name("eth_friend").unwrap();
        let eth_dos_base = eth_dos_batch.predicate_ref_by_name("eth_dos_base").unwrap();
        let eth_dos_ind = eth_dos_batch.predicate_ref_by_name("eth_dos_ind").unwrap();
        let eth_dos = eth_dos_batch.predicate_ref_by_name("eth_dos").unwrap();
        Ok(Self {
            params: params.clone(),
            vd_set: vd_set.clone(),
            mock,
            eth_friend,
            eth_dos_base,
            eth_dos_ind,
            eth_dos,
            src,
        })
    }

    pub fn dist_1(&self, src_attestation: &SignedPod) -> Result<MainPodBuilder> {
        assert_eq!(
            &self.src,
            src_attestation.get(KEY_SIGNER).expect("get KEY_SIGNER")
        );

        let mut pod = MainPodBuilder::new(&self.params, &self.vd_set);
        pod.add_signed_pod(src_attestation);

        let src_eq_src = pod.priv_op(Operation::eq(self.src.clone(), self.src.clone()))?;
        let distance_eq_zero = pod.priv_op(Operation::eq(0, 0))?;
        let eth_dos_src_to_src_base = pod.priv_op(Operation::custom(
            self.eth_dos_base.clone(),
            [src_eq_src, distance_eq_zero],
        ))?;
        let eth_dos_src_to_src = pod.priv_op(Operation::custom(
            self.eth_dos.clone(),
            [eth_dos_src_to_src_base, Statement::None],
        ))?;

        // eth_dos src->dst dist=1
        self.n_plus_1(&mut pod, eth_dos_src_to_src, src_attestation, 0)?;

        Ok(pod)
    }

    pub fn dist_n_plus_1(
        &self,
        eth_dos_src_to_int_pod: &MainPod,
        int_attestation: &SignedPod, // int signs dst
    ) -> Result<MainPodBuilder> {
        assert_eq!(
            Value::from(if self.mock {
                PodType::MockMain
            } else {
                PodType::Main
            }),
            eth_dos_src_to_int_pod.get(KEY_TYPE).expect("get KEY_TYPE")
        );

        let mut pod = MainPodBuilder::new(&self.params, &self.vd_set);
        pod.add_signed_pod(int_attestation);
        pod.add_recursive_pod(eth_dos_src_to_int_pod.clone());

        let eth_dos_int_to_dst = eth_dos_src_to_int_pod
            .pod
            .pub_statements()
            .into_iter()
            .rev() // Find the last predicate because dist_1 has two: dist=0, dist=1
            .find(|st| st.predicate() == Predicate::Custom(self.eth_dos.clone()))
            .expect("eth_dos custom predicate");
        let [_src, int, n] = {
            let args: [_; 3] = eth_dos_int_to_dst.args().try_into().expect("Vec::len=3");
            args.map(|arg| match arg {
                StatementArg::Literal(v) => v,
                _ => panic!("expected StatementArg::Literal"),
            })
        };
        assert_eq!(
            &int,
            int_attestation.get(KEY_SIGNER).expect("get KEY_SIGNER")
        );

        let n_i64 = if let TypedValue::Int(x) = n.typed() {
            *x
        } else {
            panic!("distance value is not Int")
        };

        // eth_dos src->dst dist=n+1
        self.n_plus_1(&mut pod, eth_dos_int_to_dst, int_attestation, n_i64)?;

        Ok(pod)
    }

    fn n_plus_1(
        &self,
        pod: &mut MainPodBuilder,
        eth_dos_int_to_dst: Statement,
        int_attestation: &SignedPod,
        n: i64,
    ) -> Result<()> {
        assert_eq!(
            &Value::from(PodType::Signed),
            int_attestation.get(KEY_TYPE).expect("get KEY_TYPE")
        );

        // eth_friend statement
        let attestation_is_signed_pod = int_attestation.get_statement(KEY_TYPE).unwrap();
        let attestation_signed_by_int = int_attestation.get_statement(KEY_SIGNER).unwrap();
        let int_attests_to_dst = int_attestation.get_statement("attestation").unwrap();
        let ethfriends_int_dst = pod.priv_op(Operation::custom(
            self.eth_friend.clone(),
            [
                attestation_is_signed_pod,
                attestation_signed_by_int,
                int_attests_to_dst,
            ],
        ))?;

        // distance = n + 1
        let ethdos_sum = pod.priv_op(Operation::sum_of(n + 1, n, 1))?;
        let eth_dos_src_to_dst_ind = pod.priv_op(Operation::custom(
            self.eth_dos_ind.clone(),
            [eth_dos_int_to_dst, ethdos_sum, ethfriends_int_dst],
        ))?;
        let _eth_dos_src_dst = pod.pub_op(Operation::custom(
            self.eth_dos.clone(),
            [Statement::None, eth_dos_src_to_dst_ind],
        ))?;

        Ok(())
    }
}

// GreatBoy

pub fn good_boy_sign_pod_builder(params: &Params, user: &Value, age: i64) -> SignedPodBuilder {
    let mut good_boy = SignedPodBuilder::new(params);
    good_boy.insert("user", user.clone());
    good_boy.insert("age", age);

    good_boy
}

pub fn friend_sign_pod_builder(params: &Params, friend: &Value) -> SignedPodBuilder {
    let mut friend_pod = SignedPodBuilder::new(params);
    friend_pod.insert("friend", friend.clone());

    friend_pod
}

pub fn great_boy_pod_builder(
    params: &Params,
    vd_set: &VDSet,
    good_boy_pods: [&SignedPod; 4],
    friend_pods: [&SignedPod; 2],
    good_boy_issuers: &Value,
    receiver: &Value,
) -> Result<MainPodBuilder> {
    // Attestment chain (issuer -> good boy -> great boy):
    // issuer 0 -> good_boy_pods[0] => good boy 0
    // issuer 1 -> good_boy_pods[1] => good boy 0
    // issuer 2 -> good_boy_pods[2] => good boy 1
    // issuer 3 -> good_boy_pods[3] => good boy 1
    // good boy 0 -> friend_pods[0] => receiver
    // good boy 1 -> friend_pods[1] => receiver

    let mut great_boy = MainPodBuilder::new(params, vd_set);
    for good_boy_pod in good_boy_pods {
        great_boy.add_signed_pod(good_boy_pod);
    }
    for friend_pod in friend_pods {
        great_boy.add_signed_pod(friend_pod);
    }

    for good_boy_idx in 0..2 {
        // Type check
        great_boy.pub_op(Operation::eq(
            (friend_pods[good_boy_idx], KEY_TYPE),
            PodType::Signed as i64,
        ))?;
        for issuer_idx in 0..2 {
            // Type check
            great_boy.pub_op(Operation::eq(
                (good_boy_pods[good_boy_idx * 2 + issuer_idx], KEY_TYPE),
                PodType::Signed as i64,
            ))?;
            // Each good boy POD comes from a valid issuer
            great_boy.pub_op(Operation::set_contains(
                good_boy_issuers,
                (good_boy_pods[good_boy_idx * 2 + issuer_idx], KEY_SIGNER),
            ))?;
            // Each good boy has 2 good boy pods
            great_boy.pub_op(Operation::eq(
                (good_boy_pods[good_boy_idx * 2 + issuer_idx], "user"),
                (friend_pods[good_boy_idx], KEY_SIGNER),
            ))?;
        }
        // The good boy PODs from each good boy have different issuers
        great_boy.pub_op(Operation::ne(
            (good_boy_pods[good_boy_idx * 2], KEY_SIGNER),
            (good_boy_pods[good_boy_idx * 2 + 1], KEY_SIGNER),
        ))?;
        // Each good boy is receivers' friend
        great_boy.pub_op(Operation::eq(
            (friend_pods[good_boy_idx], "friend"),
            receiver.clone(),
        ))?;
    }
    // The two good boys are different
    great_boy.pub_op(Operation::ne(
        (friend_pods[0], KEY_SIGNER),
        (friend_pods[1], KEY_SIGNER),
    ))?;

    Ok(great_boy)
}

pub fn great_boy_pod_full_flow() -> Result<MainPodBuilder> {
    let params = Params {
        max_input_signed_pods: 6,
        max_input_recursive_pods: 0,
        max_statements: 100,
        max_public_statements: 50,
        num_public_statements_id: 50,
        ..Default::default()
    };
    let vd_set = &*MOCK_VD_SET;

    let giggles_signer = Signer(SecretKey(1u32.into()));
    let macrosoft_signer = Signer(SecretKey(2u32.into()));
    let faebook_signer = Signer(SecretKey(3u32.into()));
    let good_boy_issuers =
        [&giggles_signer, &macrosoft_signer, &faebook_signer].map(|s| s.0.public_key());
    let bob_signer = Signer(SecretKey(11u32.into()));
    let charlie_signer = Signer(SecretKey(12u32.into()));
    let alice_signer = Signer(SecretKey(13u32.into()));
    let bob = bob_signer.public_key();
    let charlie = charlie_signer.public_key();
    let alice = alice_signer.public_key();

    // Bob receives two good_boy pods from Giggles and Macrosoft.

    let mut bob_good_boys = Vec::new();

    let good_boy = good_boy_sign_pod_builder(&params, &bob, 36);
    bob_good_boys.push(good_boy.sign(&giggles_signer).unwrap());
    bob_good_boys.push(good_boy.sign(&macrosoft_signer).unwrap());

    // Charlie receives two good_boy pods from Macrosoft and Faebook

    let mut charlie_good_boys = Vec::new();

    let good_boy = good_boy_sign_pod_builder(&params, &charlie, 27);
    charlie_good_boys.push(good_boy.sign(&macrosoft_signer).unwrap());
    charlie_good_boys.push(good_boy.sign(&faebook_signer).unwrap());

    // Bob and Charlie send Alice a Friend POD

    let mut alice_friend_pods = Vec::new();
    let friend = friend_sign_pod_builder(&params, &alice);
    alice_friend_pods.push(friend.sign(&bob_signer).unwrap());
    alice_friend_pods.push(friend.sign(&charlie_signer).unwrap());

    let good_boy_issuers = Value::from(Set::new(
        params.max_depth_mt_containers,
        good_boy_issuers.into_iter().map(Value::from).collect(),
    )?);

    let builder = great_boy_pod_builder(
        &params,
        vd_set,
        [
            &bob_good_boys[0],
            &bob_good_boys[1],
            &charlie_good_boys[0],
            &charlie_good_boys[1],
        ],
        [&alice_friend_pods[0], &alice_friend_pods[1]],
        &good_boy_issuers,
        &alice,
    )?;

    Ok(builder)
}

// Tickets

pub const TICKET_OWNER_SECRET_KEY: SecretKey = SecretKey(BigUint::ZERO);

pub fn tickets_sign_pod_builder(params: &Params) -> SignedPodBuilder {
    // Create a signed pod with all atomic types (string, int, bool)
    let mut builder = SignedPodBuilder::new(params);
    builder.insert("eventId", 123);
    builder.insert("productId", 456);
    // Removed temporarily to make the example fit in 8 entries.
    //builder.insert("attendeeName", "John Doe");
    builder.insert("attendeeEmail", "john.doe@example.com");
    builder.insert("attendeePublicKey", TICKET_OWNER_SECRET_KEY.public_key());
    builder.insert("isConsumed", true);
    builder.insert("isRevoked", false);
    builder
}

pub fn tickets_pod_builder(
    params: &Params,
    vd_set: &VDSet,
    signed_pod: &SignedPod,
    expected_event_id: i64,
    expect_consumed: bool,
    blacklisted_emails: &Set,
) -> Result<MainPodBuilder> {
    let blacklisted_email_set_value = Value::from(TypedValue::Set(blacklisted_emails.clone()));
    // Create a main pod referencing this signed pod with some statements
    let mut builder = MainPodBuilder::new(params, vd_set);
    builder.add_signed_pod(signed_pod);
    builder.pub_op(Operation::eq((signed_pod, "eventId"), expected_event_id))?;
    builder.pub_op(Operation::eq((signed_pod, "isConsumed"), expect_consumed))?;
    builder.pub_op(Operation::eq((signed_pod, "isRevoked"), false))?;
    builder.pub_op(Operation::dict_not_contains(
        blacklisted_email_set_value,
        (signed_pod, "attendeeEmail"),
    ))?;

    // This isn't the most fool-proof way to prove ownership (it requires
    // verifier to check pod ID on an anchored key to confirm statement wasn't
    // copied), but it's the simplest.
    let st_sk = builder.priv_literal(TICKET_OWNER_SECRET_KEY)?;
    builder.pub_op(Operation::public_key_of(
        (signed_pod, "attendeePublicKey"),
        st_sk.clone(),
    ))?;

    // Nullifier calculation is public, but based on the private sk.
    let external_nullifier = "external nullifier";
    let nullifier = hash_values(&[TICKET_OWNER_SECRET_KEY.into(), external_nullifier.into()]);
    builder.pub_op(Operation::hash_of(nullifier, st_sk, external_nullifier))?;

    Ok(builder)
}

pub fn tickets_pod_full_flow(params: &Params, vd_set: &VDSet) -> Result<MainPodBuilder> {
    let builder = tickets_sign_pod_builder(params);

    let signed_pod = builder.sign(&Signer(SecretKey(1u32.into()))).unwrap();
    tickets_pod_builder(
        params,
        vd_set,
        &signed_pod,
        123,
        true,
        &Set::new(params.max_depth_mt_containers, HashSet::new())?,
    )
}
