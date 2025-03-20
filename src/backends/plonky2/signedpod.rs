use anyhow::{anyhow, Result};
use std::any::Any;
use std::collections::HashMap;

use super::primitives::merkletree::MerkleTree;
use crate::constants::MAX_DEPTH;
use crate::middleware::{
    containers::Dictionary, hash_str, AnchoredKey, Hash, Params, Pod, PodId, PodSigner, PodType,
    Statement, Value, KEY_SIGNER, KEY_TYPE,
};

use super::primitives::signature::{PublicKey, SecretKey, Signature};

pub struct Signer(SecretKey);

impl PodSigner for Signer {
    fn sign(&mut self, _params: &Params, kvs: &HashMap<Hash, Value>) -> Result<Box<dyn Pod>> {
        let mut kvs = kvs.clone();
        let pubkey = self.0.public_key();
        kvs.insert(hash_str(KEY_SIGNER), pubkey.0);
        kvs.insert(hash_str(KEY_TYPE), Value::from(PodType::Signed));

        let dict = Dictionary::new(&kvs)?;
        let id = Value::from(dict.commitment()); // PodId as Value

        let (pp, _) = Signature::params()?; // TODO do not generate it here
        let signature: Signature = self.0.sign(&pp, id)?;
        Ok(Box::new(SignedPod {
            id: PodId(Hash::from(id)),
            signature,
            dict,
        }))
    }
}

#[derive(Clone, Debug)]
pub struct SignedPod {
    id: PodId,
    signature: Signature,
    dict: Dictionary,
}

impl Pod for SignedPod {
    fn verify(&self) -> Result<()> {
        // 1. Verify type
        let value_at_type = self.dict.get(&hash_str(KEY_TYPE).into())?;
        if Value::from(PodType::Signed) != value_at_type {
            return Err(anyhow!("type should be Signed"));
        }

        // 2. Verify id
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
            return Err(anyhow!("id does not match"));
        }

        // 3. Verify signature
        let (_, vp) = Signature::params()?; // TODO do not generate it here
        let pk_value = self.dict.get(&hash_str(KEY_SIGNER).into())?;
        let pk = PublicKey(pk_value);
        self.signature.verify(&vp, &pk, Value::from(id.0))?;

        Ok(())
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
    use crate::middleware::{self, EMPTY_HASH, F};

    #[test]
    fn test_signed_0() -> Result<()> {
        let params = middleware::Params::default();
        let mut pod = frontend::SignedPodBuilder::new(&params);
        pod.insert("idNumber", "4242424242");
        pod.insert("dateOfBirth", 1169909384);
        pod.insert("socialSecurityNumber", "G2121210");

        let sk = SecretKey::new();
        let mut signer = Signer(sk);
        let pod = pod.sign(&mut signer).unwrap();
        let pod = pod.pod.into_any().downcast::<SignedPod>().unwrap();

        pod.verify()?;
        println!("id: {}", pod.id());
        println!("kvs: {:?}", pod.kvs());

        let mut bad_pod = pod.clone();
        let (pp, _) = Signature::params()?; // TODO do not generate it here
        bad_pod.signature = signer.0.sign(&pp, Value::from(42_i64))?;
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
