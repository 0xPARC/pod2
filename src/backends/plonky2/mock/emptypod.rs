use itertools::Itertools;

use crate::{
    backends::plonky2::{
        basetypes::{Proof, VerifierOnlyCircuitData},
        error::{Error, Result},
        mainpod::{self},
    },
    middleware::{
        containers::Array, Hash, IntroPredicateRef, Params, Pod, PodType, Statement, VDSet, Value,
        EMPTY_HASH,
    },
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MockEmptyPod {
    params: Params,
    sts_root: Hash,
    vd_set: VDSet,
}

fn empty_statement() -> Statement {
    Statement::Intro(
        IntroPredicateRef {
            name: "mock_empty".to_string(),
            args_len: 0,
            verifier_data_hash: EMPTY_HASH,
        },
        vec![],
    )
}

fn sts_mt() -> Array {
    Array::new(vec![Value::from(empty_statement().hash())])
}

impl MockEmptyPod {
    pub fn new_boxed(params: &Params, vd_set: VDSet) -> Box<dyn Pod> {
        let sts_root = sts_mt().commitment();
        Box::new(Self {
            params: params.clone(),
            sts_root,
            vd_set,
        })
    }
}

impl Pod for MockEmptyPod {
    fn params(&self) -> &Params {
        &self.params
    }
    fn verify(&self) -> Result<()> {
        let _statements = self
            .pub_self_statements()
            .into_iter()
            .map(mainpod::Statement::from)
            .collect_vec();
        let sts_root = sts_mt().commitment();
        if sts_root != self.sts_root {
            return Err(Error::statements_root_not_equal(self.sts_root, sts_root));
        }
        Ok(())
    }
    fn statements_root(&self) -> Hash {
        self.sts_root
    }
    fn pod_type(&self) -> (usize, &'static str) {
        (PodType::MockEmpty as usize, "MockEmpty")
    }

    fn pub_raw_statements_mt(&self) -> Array {
        Array::new(vec![Value::from(empty_statement().hash())])
    }

    fn pub_self_statements(&self) -> Vec<Statement> {
        vec![empty_statement()]
    }

    fn verifier_data_hash(&self) -> Hash {
        EMPTY_HASH
    }
    fn verifier_data(&self) -> VerifierOnlyCircuitData {
        panic!("MockEmptyPod can't be verified in a recursive MainPod circuit");
    }
    fn common_hash(&self) -> String {
        panic!("MockEmptyPod can't be verified in a recursive MainPod circuit");
    }
    fn proof(&self) -> Proof {
        panic!("MockEmptyPod can't be verified in a recursive MainPod circuit");
    }
    fn vd_set(&self) -> &VDSet {
        &self.vd_set
    }
    fn serialize_data(&self) -> serde_json::Value {
        serde_json::Value::Null
    }
    fn deserialize_data(
        params: Params,
        _data: serde_json::Value,
        vd_set: VDSet,
        sts_root: Hash,
    ) -> Result<Self> {
        Ok(Self {
            params,
            sts_root,
            vd_set,
        })
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn test_mock_empty_pod() {
        let params = Params::default();

        let empty_pod = MockEmptyPod::new_boxed(&params, VDSet::new(&[]));
        empty_pod.verify().unwrap();
    }
}
