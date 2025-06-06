use std::collections::HashMap;

use itertools::Itertools;

use crate::{
    backends::plonky2::{
        error::{Error, Result},
        primitives::merkletree::MerkleTree,
    },
    constants::MAX_DEPTH,
    middleware::{
        containers::Dictionary, hash_str, AnchoredKey, DynError, Hash, Key, Params, Pod, PodId,
        PodSigner, PodType, RawValue, Statement, Value, KEY_SIGNER, KEY_TYPE, SELF,
    },
};

pub struct MockSigner {
    pub pk: String,
}

impl MockSigner {
    pub fn public_key(&self) -> Hash {
        hash_str(&self.pk)
    }
}

impl MockSigner {
    fn _sign(&mut self, _params: &Params, kvs: &HashMap<Key, Value>) -> Result<MockSignedPod> {
        let mut kvs = kvs.clone();
        let pubkey = self.public_key();
        kvs.insert(Key::from(KEY_SIGNER), Value::from(pubkey));
        kvs.insert(Key::from(KEY_TYPE), Value::from(PodType::MockSigned));

        let dict = Dictionary::new(kvs.clone())?;
        let id = PodId(dict.commitment());
        let signature = format!("{}_signed_by_{}", id, pubkey);
        Ok(MockSignedPod { id, signature, kvs })
    }
}

impl PodSigner for MockSigner {
    fn sign(
        &mut self,
        params: &Params,
        kvs: &HashMap<Key, Value>,
    ) -> Result<Box<dyn Pod>, Box<DynError>> {
        Ok(self._sign(params, kvs).map(Box::new)?)
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

    pub fn signature(&self) -> String {
        self.signature.clone()
    }
}

impl MockSignedPod {
    fn _verify(&self) -> Result<()> {
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
            return Err(Error::id_not_equal(self.id, id));
        }

        // 2. Verify type
        let value_at_type = self
            .kvs
            .get(&Key::from(KEY_TYPE))
            .ok_or(Error::key_not_found())?;
        if &Value::from(PodType::MockSigned) != value_at_type {
            return Err(Error::type_not_equal(
                PodType::MockSigned,
                value_at_type.clone(),
            ));
        }

        // 3. Verify signature
        let pk_hash = self
            .kvs
            .get(&Key::from(KEY_SIGNER))
            .ok_or(Error::key_not_found())?;
        let signature = format!("{}_signed_by_{}", id, pk_hash);
        if signature != self.signature {
            return Err(Error::custom(format!(
                "signature does not match, expected {}, computed {}",
                self.id, id
            )));
        }

        Ok(())
    }
}

impl Pod for MockSignedPod {
    fn params(&self) -> &Params {
        panic!("MockSignedPod doesn't have params");
    }
    fn verify(&self) -> Result<(), Box<DynError>> {
        Ok(self._verify()?)
    }

    fn id(&self) -> PodId {
        self.id
    }

    fn pub_self_statements(&self) -> Vec<Statement> {
        // By convention we put the KEY_TYPE first and KEY_SIGNER second
        let mut kvs = self.kvs.clone();
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

    fn serialized_proof(&self) -> String {
        serde_json::to_string(&self.signature).unwrap()
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
    fn test_mock_signed_0() -> Result<()> {
        let params = middleware::Params::default();
        let mut pod = frontend::SignedPodBuilder::new(&params);
        pod.insert("idNumber", "4242424242");
        pod.insert("dateOfBirth", 1169909384);
        pod.insert("socialSecurityNumber", "G2121210");

        let mut signer = MockSigner { pk: "Molly".into() };
        let pod = pod.sign(&mut signer).unwrap();
        let pod = (pod.pod as Box<dyn Any>)
            .downcast::<MockSignedPod>()
            .unwrap();

        pod._verify()?;
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
