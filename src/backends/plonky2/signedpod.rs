use std::{any::Any, collections::HashMap, sync::LazyLock};

use itertools::Itertools;
use num_bigint::{BigUint, RandBigInt};
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};

use crate::{
    backends::plonky2::{
        deserialize_bytes,
        error::{Error, Result},
        primitives::{
            ec::{
                curve::{Point, GROUP_ORDER},
                schnorr::{SecretKey, Signature},
            },
            merkletree::MerkleTree,
        },
        serialize_bytes,
    },
    middleware::{
        containers::Dictionary, AnchoredKey, Hash, Key, Params, Pod, PodId, PodSigner, PodType,
        RawValue, Statement, Value, KEY_SIGNER, KEY_TYPE, SELF,
    },
    timed,
};

pub struct Signer(pub SecretKey);

impl Signer {
    fn sign_with_nonce(
        &mut self,
        params: &Params,
        nonce: BigUint,
        kvs: &HashMap<Key, Value>,
    ) -> Result<SignedPod> {
        let mut kvs = kvs.clone();
        let pubkey = self.0.public_key();
        kvs.insert(Key::from(KEY_SIGNER), Value::from(pubkey));
        kvs.insert(Key::from(KEY_TYPE), Value::from(PodType::Signed));

        let dict = Dictionary::new(params.max_depth_mt_containers, kvs)?;
        let id = RawValue::from(dict.commitment()); // PodId as Value

        let signature: Signature = timed!("SignedPod::sign", self.0.sign(id, &nonce));
        Ok(SignedPod {
            id: PodId(Hash::from(id)),
            signature,
            signer: pubkey,
            dict,
        })
    }
    fn _sign(&mut self, params: &Params, kvs: &HashMap<Key, Value>) -> Result<SignedPod> {
        let nonce = OsRng.gen_biguint_below(&GROUP_ORDER);
        self.sign_with_nonce(params, nonce, kvs)
    }

    pub fn public_key(&self) -> Point {
        self.0.public_key()
    }
}

impl PodSigner for Signer {
    fn sign(&mut self, params: &Params, kvs: &HashMap<Key, Value>) -> Result<Box<dyn Pod>> {
        Ok(self._sign(params, kvs).map(Box::new)?)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignedPod {
    pub id: PodId,
    pub signature: Signature,
    pub signer: Point,
    pub dict: Dictionary,
}

#[derive(Serialize, Deserialize)]
struct Data {
    signer: String,
    signature: String,
    kvs: Dictionary,
}

static DUMMY_POD: LazyLock<SignedPod> = LazyLock::new(dummy);

fn dummy() -> SignedPod {
    let nonce = BigUint::from(2u32);
    Signer(SecretKey(BigUint::from(1u32)))
        .sign_with_nonce(&Params::default(), nonce, &HashMap::new())
        .expect("valid")
}

impl SignedPod {
    pub(crate) fn deserialize(id: PodId, data: serde_json::Value) -> Result<Box<dyn Pod>> {
        let data: Data = serde_json::from_value(data)?;
        let signer_bytes = deserialize_bytes(&data.signer)?;
        let signature_bytes = deserialize_bytes(&data.signature)?;

        if signer_bytes.len() != 40 {
            return Err(Error::custom(
                "Invalid byte encoding of signed POD signer.".to_string(),
            ));
        }
        if signature_bytes.len() != 80 {
            return Err(Error::custom(
                "Invalid byte encoding of signed POD signature.".to_string(),
            ));
        }

        let signer = Point::from_bytes_into_subgroup(&signer_bytes)?;
        let signature = Signature::from_bytes(&signature_bytes)?;

        Ok(Box::new(Self {
            id,
            signature,
            signer,
            dict: data.kvs,
        }))
    }

    /// Generate a valid SignedPod with a public deterministic secret key and nonce and no other
    /// key-values than the default ones.  This is used for padding.
    pub fn dummy() -> SignedPod {
        DUMMY_POD.clone()
    }
}

impl Pod for SignedPod {
    fn params(&self) -> &Params {
        panic!("SignedPod doesn't have params");
    }
    fn verify(&self) -> Result<()> {
        // 1. Verify type
        let value_at_type = self.dict.get(&Key::from(KEY_TYPE))?;
        if Value::from(PodType::Signed) != *value_at_type {
            return Err(Error::type_not_equal(
                PodType::Signed,
                value_at_type.clone(),
            ));
        }

        // 2. Verify id
        let mt = MerkleTree::new(
            self.dict.max_depth(),
            &self
                .dict
                .kvs()
                .iter()
                .map(|(k, v)| (k.raw(), v.raw()))
                .collect::<HashMap<RawValue, RawValue>>(),
        )?;
        let id = PodId(mt.root());
        if id != self.id {
            return Err(Error::id_not_equal(self.id, id));
        }

        // 3. Verify signature
        let embedded_pk_value = self.dict.get(&Key::from(KEY_SIGNER))?;
        let pk = self.signer;
        let pk_value = Value::from(pk);
        if &pk_value != embedded_pk_value {
            return Err(Error::signer_not_equal(embedded_pk_value.clone(), pk_value));
        }
        self.signature
            .verify(pk, RawValue::from(id.0))
            .then_some(())
            .ok_or(Error::custom("Invalid signature!".into()))
    }

    fn id(&self) -> PodId {
        self.id
    }
    fn pod_type(&self) -> (usize, &'static str) {
        (PodType::Signed as usize, "Signed")
    }

    fn pub_self_statements(&self) -> Vec<Statement> {
        // By convention we put the KEY_TYPE first and KEY_SIGNER second
        let mut kvs: HashMap<Key, Value> = self.dict.kvs().clone();
        let key_type = Key::from(KEY_TYPE);
        let value_type = kvs.remove(&key_type).expect("KEY_TYPE");
        let key_signer = Key::from(KEY_SIGNER);
        let value_signer = kvs.remove(&key_signer).expect("KEY_SIGNER");
        [(key_type, value_type), (key_signer, value_signer)]
            .into_iter()
            .chain(kvs.into_iter().sorted_by_key(|kv| kv.0.hash()))
            .map(|(k, v)| Statement::equal(AnchoredKey::from((SELF, k)), v))
            .collect()
    }

    fn serialize_data(&self) -> serde_json::Value {
        let signer = serialize_bytes(
            &self
                .signer
                .as_bytes_from_subgroup()
                .expect("Signer public key must lie in EC subgroup."),
        );
        let signature = serialize_bytes(&self.signature.as_bytes());
        serde_json::to_value(Data {
            signer,
            signature,
            kvs: self.dict.clone(),
        })
        .expect("serialization to json")
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
    fn equals(&self, other: &dyn Pod) -> bool {
        if let Some(other) = other.as_any().downcast_ref::<SignedPod>() {
            self == other
        } else {
            false
        }
    }
}

#[cfg(test)]
pub mod tests {
    use std::{any::Any, iter};

    use plonky2::field::types::Field;

    use super::*;
    use crate::{
        frontend,
        middleware::{self, EMPTY_VALUE, F},
    };

    #[test]
    fn test_signed_0() -> Result<()> {
        let params = middleware::Params::default();
        let mut pod = frontend::SignedPodBuilder::new(&params);
        pod.insert("idNumber", "4242424242");
        pod.insert("dateOfBirth", 1169909384);
        pod.insert("socialSecurityNumber", "G2121210");

        let sk = SecretKey(123u64.into());
        let mut signer = Signer(sk);
        let pod = pod.sign(&mut signer).unwrap();
        let pod = (pod.pod as Box<dyn Any>).downcast::<SignedPod>().unwrap();

        pod.verify()?;
        println!("id: {}", pod.id());
        println!("kvs: {:?}", pod.kvs());

        let mut bad_pod = pod.clone();
        let nonce = 456u64.into();
        bad_pod.signature = signer.0.sign(RawValue::from(42_i64), &nonce);
        assert!(bad_pod.verify().is_err());

        let mut bad_pod = pod.clone();
        bad_pod.id.0 .0[0] = F::ZERO;
        assert!(bad_pod.verify().is_err());

        let mut bad_pod = pod.clone();
        let bad_kv = (Key::from(KEY_SIGNER), Value::from(EMPTY_VALUE));
        let bad_kvs = bad_pod
            .dict
            .kvs()
            .clone()
            .into_iter()
            .chain(iter::once(bad_kv))
            .collect::<HashMap<Key, Value>>();
        bad_pod.dict = Dictionary::new(params.max_depth_mt_containers, bad_kvs).unwrap();
        assert!(bad_pod.verify().is_err());

        let mut bad_pod = pod.clone();
        let bad_kv = (Key::from(KEY_TYPE), Value::from(0));
        let bad_kvs = bad_pod
            .dict
            .kvs()
            .clone()
            .into_iter()
            .chain(iter::once(bad_kv))
            .collect::<HashMap<Key, Value>>();
        bad_pod.dict = Dictionary::new(params.max_depth_mt_containers, bad_kvs).unwrap();
        assert!(bad_pod.verify().is_err());

        Ok(())
    }
}
