use std::{any::Any, collections::HashMap};

use anyhow::{anyhow, Result};
use itertools::Itertools;

use crate::{
    backends::plonky2::primitives::merkletree::MerkleTree,
    constants::MAX_DEPTH,
    middleware::{
        containers::Dictionary, hash_str, AnchoredKey, Hash, Key, Params, Pod, PodId, PodSigner,
        PodType, RawValue, Statement, Value, KEY_SIGNER, KEY_TYPE,
    },
};

pub struct MockSigner {
    pub pk: String,
}

impl MockSigner {
    pub fn pubkey(&self) -> Hash {
        hash_str(&self.pk)
    }
}

impl PodSigner for MockSigner {
    fn sign(&mut self, _params: &Params, kvs: &HashMap<Key, Value>) -> Result<Box<dyn Pod>> {
        let mut kvs = kvs.clone();
        let pubkey = self.pubkey();
        kvs.insert(Key::from(KEY_SIGNER), Value::from(pubkey));
        kvs.insert(Key::from(KEY_TYPE), Value::from(PodType::MockSigned));

        let dict = Dictionary::new(kvs.clone())?;
        let id = PodId(dict.commitment());
        let signature = format!("{}_signed_by_{}", id, pubkey);
        Ok(Box::new(MockSignedPod { id, signature, kvs }))
    }
}

#[derive(Clone, Debug)]
pub struct MockSignedPod {
    id: PodId,
    signature: String,
    kvs: HashMap<Key, Value>,
}

impl MockSignedPod {
    pub(crate) fn new(id: PodId, signature: String, kvs: HashMap<Key, Value>) -> Self {
        Self { id, signature, kvs }
    }
}

impl Pod for MockSignedPod {
    fn verify(&self) -> Result<()> {
        // 1. Verify id
        let mt = MerkleTree::new(
            MAX_DEPTH,
            &self
                .kvs
                .iter()
                .map(|(k, v)| (k.raw(), v.raw()))
                .collect::<HashMap<RawValue, RawValue>>(),
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
        let value_at_type = self
            .kvs
            .get(&Key::from(KEY_TYPE))
            .ok_or(anyhow!("key not found"))?;
        if &Value::from(PodType::MockSigned) != value_at_type {
            return Err(anyhow!(
                "type does not match, expected MockSigned ({}), found {}",
                PodType::MockSigned,
                value_at_type
            ));
        }

        // 3. Verify signature
        let pk_hash = self
            .kvs
            .get(&Key::from(KEY_SIGNER))
            .ok_or(anyhow!("key not found"))?;
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
        let mut kvs = self.kvs.clone();
        let key_type = Key::from(KEY_TYPE);
        let value_type = kvs.remove(&key_type).expect("KEY_TYPE");
        let key_signer = Key::from(KEY_SIGNER);
        let value_signer = kvs.remove(&key_signer).expect("KEY_SIGNER");
        [(key_type, value_type), (key_signer, value_signer)]
            .into_iter()
            .chain(kvs.into_iter().sorted_by_key(|kv| kv.0.hash()))
            .map(|(k, v)| Statement::ValueOf(AnchoredKey::from((id, k)), v))
            .collect()
    }

    fn into_any(self: Box<Self>) -> Box<dyn Any> {
        self
    }
    fn as_any(&self) -> &dyn Any {
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
        frontend,
        middleware::{self, EMPTY_VALUE, F},
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
        let bad_kv = (Key::from(KEY_SIGNER), Value::from(EMPTY_VALUE));
        let bad_kvs = bad_pod
            .kvs
            .clone()
            .into_iter()
            .chain(iter::once(bad_kv))
            .collect::<HashMap<Key, Value>>();
        bad_pod.kvs = bad_kvs;
        assert!(bad_pod.verify().is_err());

        let mut bad_pod = pod.clone();
        let bad_kv = (Key::from(KEY_TYPE), Value::from(0));
        let bad_kvs = bad_pod
            .kvs
            .clone()
            .into_iter()
            .chain(iter::once(bad_kv))
            .collect::<HashMap<Key, Value>>();
        bad_pod.kvs = bad_kvs;
        assert!(bad_pod.verify().is_err());

        Ok(())
    }
}
