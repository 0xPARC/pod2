use std::{any::Any, collections::HashMap};

use anyhow::{anyhow, Result};
use itertools::Itertools;

use crate::{
    backends::plonky2::primitives::merkletree::MerkleTree,
    constants::MAX_DEPTH,
    middleware::{
        containers::Dictionary, hash_str, AnchoredKey, Hash, Params, Pod, PodId, PodSigner,
        PodType, Statement, Value, KEY_SIGNER, KEY_TYPE,
    },
};

pub struct MockSigner {
    pub pk: String,
}

impl MockSigner {
    pub fn pubkey(&self) -> Value {
        Value(hash_str(&self.pk).0)
    }
}

impl PodSigner for MockSigner {
    fn sign(&mut self, _params: &Params, kvs: &HashMap<Hash, Value>) -> Result<Box<dyn Pod>> {
        let mut kvs = kvs.clone();
        let pubkey = self.pubkey();
        kvs.insert(hash_str(KEY_SIGNER), pubkey);
        kvs.insert(hash_str(KEY_TYPE), Value::from(PodType::MockSigned));

        let dict = Dictionary::new(&kvs)?;
        let id = PodId(dict.commitment());
        let signature = format!("{}_signed_by_{}", id, pubkey);
        Ok(Box::new(MockSignedPod {
            dict,
            id,
            signature,
        }))
    }
}

#[derive(Clone, Debug)]
pub struct MockSignedPod {
    id: PodId,
    signature: String,
    dict: Dictionary,
}

impl MockSignedPod {
    pub fn deserialize(id: PodId, signature: String, dict: Dictionary) -> Self {
        Self {
            id,
            signature,
            dict,
        }
    }
}

impl Pod for MockSignedPod {
    fn verify(&self) -> Result<()> {
        // 1. Verify id
        let mt = MerkleTree::new(
            MAX_DEPTH,
            &self
                .dict
                .iter()
                .map(|(&k, &v)| (k, v))
                .collect::<HashMap<Value, Value>>(),
        )?;
        let id = PodId(mt.root());
        if id != self.id {
            return Err(anyhow!(
                "id does not match, expected {}, computed {}",
                self.id,
                id
            ));
        }

        // 2. Verify type
        let value_at_type = self.dict.get(&hash_str(KEY_TYPE).into())?;
        if Value::from(PodType::MockSigned) != value_at_type {
            return Err(anyhow!(
                "type does not match, expected MockSigned ({}), found {}",
                PodType::MockSigned,
                value_at_type
            ));
        }

        // 3. Verify signature
        let pk_hash = self.dict.get(&hash_str(KEY_SIGNER).into())?;
        let signature = format!("{}_signed_by_{}", id, pk_hash);
        if signature != self.signature {
            return Err(anyhow!(
                "signature does not match, expected {}, computed {}",
                self.id,
                id
            ));
        }

        Ok(())
    }

    fn id(&self) -> PodId {
        self.id
    }

    fn pub_statements(&self) -> Vec<Statement> {
        let id = self.id();
        // By convention we put the KEY_TYPE first and KEY_SIGNER second
        let mut kvs: HashMap<_, _> = self.dict.iter().collect();
        let key_type = Value::from(hash_str(KEY_TYPE));
        let value_type = kvs.remove(&key_type).expect("KEY_TYPE");
        let key_signer = Value::from(hash_str(KEY_SIGNER));
        let value_signer = kvs.remove(&key_signer).expect("KEY_SIGNER");
        [(&key_type, value_type), (&key_signer, value_signer)]
            .into_iter()
            .chain(kvs.into_iter().sorted_by_key(|kv| kv.0))
            .map(|(k, v)| Statement::ValueOf(AnchoredKey(id, Hash(k.0)), *v))
            .collect()
    }

    fn into_any(self: Box<Self>) -> Box<dyn Any> {
        self
    }

    fn serialized_proof(&self) -> String {
        self.signature.to_string()
    }
}

#[cfg(test)]
pub mod tests {
    use std::iter;

    use plonky2::field::types::Field;

    use super::*;
    use crate::{
        constants::MAX_DEPTH,
        frontend,
        middleware::{self, EMPTY_HASH, F},
    };

    #[test]
    fn test_mock_signed_0() -> Result<()> {
        let params = middleware::Params::default();
        let mut pod = frontend::SignedPodBuilder::new(&params);
        pod.insert("idNumber", "4242424242");
        pod.insert("dateOfBirth", 1169909384);
        pod.insert("socialSecurityNumber", "G2121210");

        let mut signer = MockSigner { pk: "Molly".into() };
        let pod = pod.sign(&mut signer).unwrap();
        let pod = pod.pod.into_any().downcast::<MockSignedPod>().unwrap();

        pod.verify()?;
        println!("id: {}", pod.id());
        println!("kvs: {:?}", pod.kvs());

        let mut bad_pod = pod.clone();
        bad_pod.signature = "".into();
        assert!(bad_pod.verify().is_err());

        let mut bad_pod = pod.clone();
        bad_pod.id.0 .0[0] = F::ZERO;
        assert!(bad_pod.verify().is_err());

        let mut bad_pod = pod.clone();
        let bad_kv = (hash_str(KEY_SIGNER).into(), Value(PodId(EMPTY_HASH).0 .0));
        let bad_kvs_mt = &bad_pod
            .kvs()
            .into_iter()
            .map(|(AnchoredKey(_, k), v)| (Value(k.0), v))
            .chain(iter::once(bad_kv))
            .collect::<HashMap<Value, Value>>();
        let bad_mt = MerkleTree::new(MAX_DEPTH, bad_kvs_mt)?;
        bad_pod.dict.mt = bad_mt;
        assert!(bad_pod.verify().is_err());

        let mut bad_pod = pod.clone();
        let bad_kv = (hash_str(KEY_TYPE).into(), Value::from(0));
        let bad_kvs_mt = &bad_pod
            .kvs()
            .into_iter()
            .map(|(AnchoredKey(_, k), v)| (Value(k.0), v))
            .chain(iter::once(bad_kv))
            .collect::<HashMap<Value, Value>>();
        let bad_mt = MerkleTree::new(MAX_DEPTH, bad_kvs_mt)?;
        bad_pod.dict.mt = bad_mt;
        assert!(bad_pod.verify().is_err());

        Ok(())
    }
}
