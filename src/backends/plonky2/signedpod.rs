use std::collections::HashMap;

use itertools::Itertools;

use crate::{
    backends::plonky2::{
        error::{Error, Result},
        primitives::{
            merkletree::MerkleTree,
            signature::{PublicKey, SecretKey, Signature},
        },
    },
    constants::MAX_DEPTH,
    middleware::{
        containers::Dictionary, AnchoredKey, DynError, Hash, Key, Params, Pod, PodId, PodSigner,
        PodType, RawValue, Statement, Value, KEY_SIGNER, KEY_TYPE,
    },
};

pub struct Signer(pub SecretKey);

impl Signer {
    fn _sign(&mut self, _params: &Params, kvs: &HashMap<Key, Value>) -> Result<SignedPod> {
        let mut kvs = kvs.clone();
        let pubkey = self.0.public_key();
        kvs.insert(Key::from(KEY_SIGNER), Value::from(pubkey.0));
        kvs.insert(Key::from(KEY_TYPE), Value::from(PodType::Signed));

        let dict = Dictionary::new(kvs)?;
        let id = RawValue::from(dict.commitment()); // PodId as Value

        let signature: Signature = self.0.sign(id)?;
        Ok(SignedPod {
            id: PodId(Hash::from(id)),
            signature,
            dict,
        })
    }

    pub fn public_key(&self) -> PublicKey {
        self.0.public_key()
    }
}

impl PodSigner for Signer {
    fn sign(
        &mut self,
        params: &Params,
        kvs: &HashMap<Key, Value>,
    ) -> Result<Box<dyn Pod>, Box<DynError>> {
        Ok(self._sign(params, kvs).map(Box::new)?)
    }
}

#[derive(Clone, Debug)]
pub struct SignedPod {
    pub id: PodId,
    pub signature: Signature,
    pub dict: Dictionary,
}

impl SignedPod {
    fn _verify(&self) -> Result<()> {
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
            MAX_DEPTH,
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
        let pk_value = self.dict.get(&Key::from(KEY_SIGNER))?;
        let pk = PublicKey(pk_value.raw());
        self.signature.verify(&pk, RawValue::from(id.0))?;

        Ok(())
    }
}

impl Pod for SignedPod {
    fn verify(&self) -> Result<(), Box<DynError>> {
        Ok(self._verify().map_err(Box::new)?)
    }

    fn id(&self) -> PodId {
        self.id
    }

    fn pub_statements(&self) -> Vec<Statement> {
        let id = self.id();
        // By convention we put the KEY_TYPE first and KEY_SIGNER second
        let mut kvs: HashMap<Key, Value> = self.dict.kvs().clone();
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

    fn serialized_proof(&self) -> String {
        let mut buffer = Vec::new();
        use plonky2::util::serialization::Write;
        buffer.write_proof(&self.signature.0).unwrap();
        hex::encode(buffer)
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

        // TODO: Use a deterministic secret key to get deterministic tests
        let sk = SecretKey::new_rand();
        let mut signer = Signer(sk);
        let pod = pod.sign(&mut signer).unwrap();
        let pod = (pod.pod as Box<dyn Any>).downcast::<SignedPod>().unwrap();

        pod._verify()?;
        println!("id: {}", pod.id());
        println!("kvs: {:?}", pod.kvs());

        let mut bad_pod = pod.clone();
        bad_pod.signature = signer.0.sign(RawValue::from(42_i64))?;
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
        bad_pod.dict = Dictionary::new(bad_kvs).unwrap();
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
        bad_pod.dict = Dictionary::new(bad_kvs).unwrap();
        assert!(bad_pod.verify().is_err());

        Ok(())
    }
}
