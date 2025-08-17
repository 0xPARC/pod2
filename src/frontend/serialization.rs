use std::collections::HashMap;

use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use super::Error;
use crate::{
    frontend::{MainPod, SignedPod},
    middleware::{
        deserialize_pod, deserialize_signed_pod, Key, Params, PodId, Statement, VDSet, Value,
    },
};

#[derive(Serialize, Deserialize, JsonSchema, Debug, Clone, PartialEq)]
#[serde(rename_all = "camelCase")]
#[schemars(rename = "SignedPod")]
pub struct SerializedSignedPod {
    pod_type: (usize, String),
    id: PodId,
    entries: HashMap<Key, Value>,
    data: serde_json::Value,
}

impl SerializedSignedPod {
    pub fn id(&self) -> PodId {
        self.id
    }
}

#[derive(Serialize, Deserialize, JsonSchema, Debug, Clone, PartialEq)]
#[serde(rename_all = "camelCase")]
#[schemars(rename = "MainPod")]
pub struct SerializedMainPod {
    params: Params,
    pod_type: (usize, String),
    id: PodId,
    vd_set: VDSet,
    public_statements: Vec<Statement>,
    data: serde_json::Value,
}

impl SerializedMainPod {
    pub fn id(&self) -> PodId {
        self.id
    }
}

impl From<SignedPod> for SerializedSignedPod {
    fn from(pod: SignedPod) -> Self {
        let (pod_type, pod_type_name_str) = pod.pod.pod_type();
        let data = pod.pod.serialize_data();
        SerializedSignedPod {
            pod_type: (pod_type, pod_type_name_str.to_string()),
            id: pod.id(),
            entries: pod.kvs().clone(),
            data,
        }
    }
}

impl TryFrom<SerializedSignedPod> for SignedPod {
    type Error = Error;

    fn try_from(serialized: SerializedSignedPod) -> Result<Self, Self::Error> {
        let pod = deserialize_signed_pod(serialized.pod_type.0, serialized.id, serialized.data)?;
        let kvs = pod.kvs().into_iter().map(|(ak, v)| (ak.key, v)).collect();
        Ok(Self { pod, kvs })
    }
}

impl From<MainPod> for SerializedMainPod {
    fn from(pod: MainPod) -> Self {
        let (pod_type, pod_type_name_str) = pod.pod.pod_type();
        let data = pod.pod.serialize_data();
        SerializedMainPod {
            pod_type: (pod_type, pod_type_name_str.to_string()),
            id: pod.id(),
            vd_set: pod.pod.vd_set().clone(),
            params: pod.params.clone(),
            public_statements: pod.pod.pub_statements(),
            data,
        }
    }
}

impl TryFrom<SerializedMainPod> for MainPod {
    type Error = Error;

    fn try_from(serialized: SerializedMainPod) -> Result<Self, Self::Error> {
        let pod = deserialize_pod(
            serialized.pod_type.0,
            serialized.params.clone(),
            serialized.id,
            serialized.vd_set,
            serialized.data,
        )?;
        let public_statements = pod.pub_statements();
        Ok(Self {
            pod,
            public_statements,
            params: serialized.params,
        })
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{HashMap, HashSet};

    use pretty_assertions::assert_eq;
    use schemars::schema_for;

    use super::*;
    use crate::{
        backends::plonky2::{
            mainpod::{rec_main_pod_circuit_data, Prover},
            mock::mainpod::MockProver,
            primitives::ec::schnorr::SecretKey,
            signedpod::Signer,
        },
        examples::{
            attest_eth_friend, zu_kyc_pod_builder, zu_kyc_sign_pod_builders, EthDosHelper,
            MOCK_VD_SET,
        },
        frontend::{Result, SignedPodBuilder},
        middleware::{
            self,
            containers::{Array, Dictionary, Set},
            Params, TypedValue, DEFAULT_VD_LIST,
        },
    };

    #[test]
    fn test_value_serialization() {
        let params = &Params::default();
        // Pairs of values and their expected serialized representations
        let values = vec![
            (TypedValue::String("hello".to_string()), "\"hello\""),
            (TypedValue::Int(42), "{\"Int\":\"42\"}"),
            (TypedValue::Bool(true), "true"),
            (
                TypedValue::Array(Array::new(params.max_depth_mt_containers, vec!["foo".into(), false.into()]).unwrap()),
                "{\"max_depth\":32,\"array\":[\"foo\",false]}",
            ),
            (
                TypedValue::Dictionary(
                    Dictionary::new(params.max_depth_mt_containers, HashMap::from([
                        // The set of valid keys is equal to the set of valid JSON keys
                        ("foo".into(), 123.into()),
                        // Empty strings are valid JSON keys
                        (("".into()), "baz".into()),
                        // Keys can contain whitespace
                        (("    hi".into()), false.into()),
                        // Keys can contain special characters
                        (("!@£$%^&&*()".into()), "".into()),
                        // Keys can contain _very_ special characters
                        (("\0".into()), "".into()),
                        // Keys can contain emojis
                        (("🥳".into()), "party time!".into()),
                    ]))
                    .unwrap(),
                ),
                "{\"max_depth\":32,\"kvs\":{\"\":\"baz\",\"\\u0000\":\"\",\"    hi\":false,\"!@£$%^&&*()\":\"\",\"foo\":{\"Int\":\"123\"},\"🥳\":\"party time!\"}}",
            ),
            (
                TypedValue::Set(Set::new(params.max_depth_mt_containers, HashSet::from(["foo".into(), "bar".into()])).unwrap()),
                "{\"max_depth\":32,\"set\":[\"bar\",\"foo\"]}",
            ),
        ];

        for (value, expected) in values {
            let serialized = serde_json::to_string(&value).unwrap();
            assert_eq!(serialized, expected);
            let deserialized: TypedValue = serde_json::from_str(&serialized).unwrap();
            assert_eq!(
                value, deserialized,
                "value {:#?} should equal deserialized {:#?}",
                value, deserialized
            );
            let expected_deserialized: TypedValue = serde_json::from_str(expected).unwrap();
            assert_eq!(value, expected_deserialized);
        }
    }

    fn signed_pod_builder() -> SignedPodBuilder {
        let params = &Params::default();
        let mut builder = SignedPodBuilder::new(params);
        builder.insert("name", "test");
        builder.insert("age", 30);
        builder.insert("very_large_int", 1152921504606846976);
        builder.insert(
            "a_dict_containing_one_key",
            Dictionary::new(
                params.max_depth_mt_containers,
                HashMap::from([
                    ("foo".into(), 123.into()),
                    (
                        "an_array_containing_three_ints".into(),
                        Array::new(
                            params.max_depth_mt_containers,
                            vec![1.into(), 2.into(), 3.into()],
                        )
                        .unwrap()
                        .into(),
                    ),
                    (
                        "a_set_containing_two_strings".into(),
                        Set::new(
                            params.max_depth_mt_containers,
                            HashSet::from([
                                Array::new(
                                    params.max_depth_mt_containers,
                                    vec!["foo".into(), "bar".into()],
                                )
                                .unwrap()
                                .into(),
                                "baz".into(),
                            ]),
                        )
                        .unwrap()
                        .into(),
                    ),
                ]),
            )
            .unwrap(),
        );
        builder
    }

    #[test]
    fn test_signed_pod_serialization() {
        let builder = signed_pod_builder();
        let signer = Signer(SecretKey(1u32.into()));
        let pod = builder.sign(&signer).unwrap();

        let serialized = serde_json::to_string_pretty(&pod).unwrap();
        println!("serialized: {}", serialized);
        let deserialized: SignedPod = serde_json::from_str(&serialized).unwrap();
        println!(
            "deserialized: {}",
            serde_json::to_string_pretty(&deserialized).unwrap()
        );
        assert_eq!(pod.kvs, deserialized.kvs);
        assert_eq!(pod.verify().is_ok(), deserialized.verify().is_ok());
        assert_eq!(pod.id(), deserialized.id())
    }

    #[test]
    fn test_mock_signed_pod_serialization() {
        let builder = signed_pod_builder();
        let signer = Signer(SecretKey(1u32.into()));
        let pod = builder.sign(&signer).unwrap();

        let serialized = serde_json::to_string_pretty(&pod).unwrap();
        println!("serialized: {}", serialized);
        let deserialized: SignedPod = serde_json::from_str(&serialized).unwrap();
        println!(
            "deserialized: {}",
            serde_json::to_string_pretty(&deserialized).unwrap()
        );
        assert_eq!(pod.kvs, deserialized.kvs);
        assert_eq!(pod.verify().is_ok(), deserialized.verify().is_ok());
        assert_eq!(pod.id(), deserialized.id())
    }

    fn build_mock_zukyc_pod() -> Result<MainPod> {
        let params = middleware::Params::default();
        let vd_set = &*MOCK_VD_SET;

        let (gov_id_builder, pay_stub_builder) = zu_kyc_sign_pod_builders(&params);
        let signer = Signer(SecretKey(1u32.into()));
        let gov_id_pod = gov_id_builder.sign(&signer).unwrap();
        let signer = Signer(SecretKey(2u32.into()));
        let pay_stub_pod = pay_stub_builder.sign(&signer).unwrap();
        let kyc_builder = zu_kyc_pod_builder(&params, vd_set, &gov_id_pod, &pay_stub_pod).unwrap();

        let prover = MockProver {};
        let kyc_pod = kyc_builder.prove(&prover).unwrap();
        Ok(kyc_pod)
    }

    fn build_plonky2_zukyc_pod() -> Result<MainPod> {
        let params = middleware::Params {
            // Currently the circuit uses random access that only supports vectors of length 64.
            // With max_input_main_pods=3 we need random access to a vector of length 73.
            max_input_recursive_pods: 1,
            ..Default::default()
        };
        let mut vds = DEFAULT_VD_LIST.clone();
        vds.push(rec_main_pod_circuit_data(&params).1.verifier_only.clone());
        let vd_set = VDSet::new(params.max_depth_mt_vds, &vds).unwrap();

        let (gov_id_builder, pay_stub_builder) = zu_kyc_sign_pod_builders(&params);
        let signer = Signer(SecretKey(1u32.into()));
        let gov_id_pod = gov_id_builder.sign(&signer)?;
        let signer = Signer(SecretKey(2u32.into()));
        let pay_stub_pod = pay_stub_builder.sign(&signer)?;
        let kyc_builder = zu_kyc_pod_builder(&params, &vd_set, &gov_id_pod, &pay_stub_pod)?;

        let prover = Prover {};
        let kyc_pod = kyc_builder.prove(&prover)?;

        Ok(kyc_pod)
    }

    #[test]
    fn test_mock_main_pod_serialization() -> Result<()> {
        let kyc_pod = build_mock_zukyc_pod()?;
        let serialized = serde_json::to_string_pretty(&kyc_pod).unwrap();
        println!("serialized: {}", serialized);
        let deserialized: MainPod = serde_json::from_str(&serialized).unwrap();

        assert_eq!(kyc_pod.public_statements, deserialized.public_statements);
        assert_eq!(kyc_pod.pod.id(), deserialized.pod.id());
        assert_eq!(kyc_pod.pod.verify()?, deserialized.pod.verify()?);

        Ok(())
    }

    #[test]
    fn test_plonky2_main_pod_serialization() -> Result<()> {
        let kyc_pod = build_plonky2_zukyc_pod()?;
        let serialized = serde_json::to_string_pretty(&kyc_pod).unwrap();
        let deserialized: MainPod = serde_json::from_str(&serialized).unwrap();

        assert_eq!(kyc_pod.public_statements, deserialized.public_statements);
        assert_eq!(kyc_pod.pod.id(), deserialized.pod.id());
        assert_eq!(kyc_pod.pod.verify()?, deserialized.pod.verify()?);

        Ok(())
    }

    fn build_ethdos_pod() -> Result<MainPod> {
        let params = Params {
            max_input_pods_public_statements: 8,
            max_statements: 24,
            max_public_statements: 8,
            ..Default::default()
        };
        let vd_set = &*MOCK_VD_SET;

        let alice = Signer(SecretKey(1u32.into()));
        let bob = Signer(SecretKey(2u32.into()));
        let charlie = Signer(SecretKey(3u32.into()));

        // Alice attests that she is ETH friends with Bob and Bob
        // attests that he is ETH friends with Charlie.
        let alice_attestation = attest_eth_friend(&params, &alice, bob.public_key());
        let bob_attestation = attest_eth_friend(&params, &bob, charlie.public_key());

        let helper = EthDosHelper::new(&params, vd_set, true, alice.public_key())?;
        let prover = MockProver {};
        let dist_1 = helper.dist_1(&alice_attestation)?.prove(&prover)?;
        let dist_2 = helper
            .dist_n_plus_1(&dist_1, &bob_attestation)?
            .prove(&prover)?;

        Ok(dist_2)
    }

    #[test]
    // This tests that we can generate JSON Schemas for the MainPod and
    // SignedPod types, and that we can validate Signed and Main Pods
    // against the schemas. Since both Mock and Plonky2 PODs have the same
    // public interface, we can assume that the schema works for both.
    fn test_schema() {
        let mainpod_schema = schema_for!(SerializedMainPod);
        let signedpod_schema = schema_for!(SerializedSignedPod);

        let kyc_pod = build_mock_zukyc_pod().unwrap();
        let signed_pod = signed_pod_builder()
            .sign(&Signer(SecretKey(1u32.into())))
            .unwrap();
        let ethdos_pod = build_ethdos_pod().unwrap();
        let mainpod_schema_value = serde_json::to_value(&mainpod_schema).unwrap();
        let signedpod_schema_value = serde_json::to_value(&signedpod_schema).unwrap();

        let kyc_pod_value = serde_json::to_value(&kyc_pod).unwrap();
        let mainpod_valid = jsonschema::validate(&mainpod_schema_value, &kyc_pod_value);
        assert!(mainpod_valid.is_ok(), "{:#?}", mainpod_valid);

        let signed_pod_value = serde_json::to_value(&signed_pod).unwrap();
        let signedpod_valid = jsonschema::validate(&signedpod_schema_value, &signed_pod_value);
        assert!(signedpod_valid.is_ok(), "{:#?}", signedpod_valid);

        let ethdos_pod_value = serde_json::to_value(&ethdos_pod).unwrap();
        let ethdos_pod_valid = jsonschema::validate(&mainpod_schema_value, &ethdos_pod_value);
        assert!(ethdos_pod_valid.is_ok(), "{:#?}", ethdos_pod_valid);
    }
}
