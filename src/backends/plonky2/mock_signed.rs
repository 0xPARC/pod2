use anyhow::Result;
use std::any::Any;
use std::collections::HashMap;

use super::primitives::merkletree::MerkleTree;
use crate::constants::MAX_DEPTH;
use crate::middleware::{
    containers::Dictionary, hash_str, AnchoredKey, Hash, Params, Pod, PodId, PodSigner, PodType,
    Statement, Value, KEY_SIGNER, KEY_TYPE,
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
    fn verify(&self) -> bool {
        // 1. Verify type
        let value_at_type = match self.dict.get(&hash_str(KEY_TYPE).into()) {
            Ok(v) => v,
            Err(_) => return false,
        };
        if Value::from(PodType::MockSigned) != value_at_type {
            return false;
        }

        // 2. Verify id
        let mt = match MerkleTree::new(
            MAX_DEPTH,
            &self
                .dict
                .iter()
                .map(|(&k, &v)| (k, v))
                .collect::<HashMap<Value, Value>>(),
        ) {
            Ok(mt) => mt,
            Err(_) => return false,
        };
        let id = PodId(mt.root());
        if id != self.id {
            return false;
        }

        // 3. Verify signature
        let pk_hash = match self.dict.get(&hash_str(KEY_SIGNER).into()) {
            Ok(v) => v,
            Err(_) => return false,
        };
        let signature = format!("{}_signed_by_{}", id, pk_hash);
        if signature != self.signature {
            return false;
        }

        true
    }

    fn id(&self) -> PodId {
        self.id
    }

    fn pub_statements(&self) -> Vec<Statement> {
        let id = self.id();
        self.dict
            .iter()
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
    use plonky2::field::types::Field;
    use std::iter;

    use super::*;
    use crate::constants::MAX_DEPTH;
    use crate::frontend;
    use crate::middleware::{self, EMPTY_HASH, F};

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

        assert!(pod.verify());
        println!("id: {}", pod.id());
        println!("kvs: {:?}", pod.kvs());

        let mut bad_pod = pod.clone();
        bad_pod.signature = "".into();
        assert!(!bad_pod.verify());

        let mut bad_pod = pod.clone();
        bad_pod.id.0 .0[0] = F::ZERO;
        assert!(!bad_pod.verify());

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
        assert!(!bad_pod.verify());

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
        assert!(!bad_pod.verify());

        Ok(())
    }
}
