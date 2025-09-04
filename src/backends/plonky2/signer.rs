use num_bigint::{BigUint, RandBigInt};
use rand::rngs::OsRng;

use crate::{
    backends::plonky2::primitives::ec::{
        curve::{Point as PublicKey, GROUP_ORDER},
        schnorr::{SecretKey, Signature},
    },
    middleware::{self, RawValue},
    timed,
};

pub struct Signer(pub SecretKey);

impl Signer {
    pub(crate) fn sign_with_nonce(&self, nonce: BigUint, msg: RawValue) -> Signature {
        let signature: Signature = timed!("SignedPod::sign", self.0.sign(msg, &nonce));
        signature
    }
}

impl middleware::Signer for Signer {
    fn sign(&self, msg: RawValue) -> Signature {
        let nonce = OsRng.gen_biguint_below(&GROUP_ORDER);
        self.sign_with_nonce(nonce, msg)
    }

    fn public_key(&self) -> PublicKey {
        self.0.public_key()
    }
}
