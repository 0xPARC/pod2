use anyhow::Result;
use std::any::Any;
use std::collections::HashMap;

use crate::constants::MAX_DEPTH;
use crate::middleware::{
    containers::Dictionary, hash_str, AnchoredKey, Hash, Params, Pod, PodId, PodSigner, PodType,
    Statement, Value, KEY_SIGNER, KEY_TYPE,
};
use crate::primitives::merkletree::MerkleTree;

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
        kvs.insert(hash_str(&KEY_SIGNER), pubkey);
        kvs.insert(hash_str(&KEY_TYPE), Value::from(PodType::MockSigned));

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

impl Pod for MockSignedPod {
    fn verify(&self) -> bool {
        // Verify type
        let value_at_type = match self.dict.get(&hash_str(&KEY_TYPE).into()) {
            Ok(v) => v,
            Err(_) => return false,
        };
        if Value::from(PodType::MockSigned) != value_at_type {
            return false;
        }

        // Verify id
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

        // Verify signature
        let pk_hash = match self.dict.get(&hash_str(&KEY_SIGNER).into()) {
            Ok(v) => v,
            Err(_) => return false,
        };
        let signature = format!("{}_signed_by_{}", id, pk_hash);
        if signature != self.signature {
            return false;
        }

        return true;
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
}

#[cfg(test)]
pub mod tests {
    use plonky2::field::types::Field;
    use std::iter;

    use super::*;
    use crate::constants::MAX_DEPTH;
    use crate::frontend;
    use crate::middleware::{self, F, NULL};

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

        assert_eq!(pod.verify(), true);
        println!("id: {}", pod.id());
        println!("kvs: {:?}", pod.kvs());

        let mut bad_pod = pod.clone();
        bad_pod.signature = "".into();
        assert_eq!(bad_pod.verify(), false);

        let mut bad_pod = pod.clone();
        bad_pod.id.0 .0[0] = F::ZERO;
        assert_eq!(bad_pod.verify(), false);

        let mut bad_pod = pod.clone();
        let bad_kv = (hash_str(KEY_SIGNER).into(), Value(PodId(NULL).0 .0));
        let bad_kvs_mt = &bad_pod
            .kvs()
            .into_iter()
            .map(|(AnchoredKey(_, k), v)| (Value(k.0), v))
            .chain(iter::once(bad_kv))
            .collect::<HashMap<Value, Value>>();
        let bad_mt = MerkleTree::new(MAX_DEPTH, &bad_kvs_mt)?;
        bad_pod.dict.mt = bad_mt;
        assert_eq!(bad_pod.verify(), false);

        let mut bad_pod = pod.clone();
        let bad_kv = (hash_str(KEY_TYPE).into(), Value::from(0));
        let bad_kvs_mt = &bad_pod
            .kvs()
            .into_iter()
            .map(|(AnchoredKey(_, k), v)| (Value(k.0), v))
            .chain(iter::once(bad_kv))
            .collect::<HashMap<Value, Value>>();
        let bad_mt = MerkleTree::new(MAX_DEPTH, &bad_kvs_mt)?;
        bad_pod.dict.mt = bad_mt;
        assert_eq!(bad_pod.verify(), false);

        Ok(())
    }
}
