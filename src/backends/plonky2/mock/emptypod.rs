use itertools::Itertools;

use crate::{
    backends::plonky2::{
        basetypes::{Proof, VerifierOnlyCircuitData},
        error::{Error, Result},
        mainpod::{self, calculate_sts_hash},
    },
    middleware::{
        AnchoredKey, Hash, IntroPredicateRef, Params, Pod, PodType, RecursivePod, Statement, VDSet,
        Value, EMPTY_HASH, KEY_TYPE,
    },
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MockEmptyPod {
    params: Params,
    sts_hash: Hash,
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

// fn type_statement() -> Statement {
//     Statement::equal(
//         AnchoredKey::from((SELF, KEY_TYPE)),
//         Value::from(PodType::Empty),
//     )
// }

impl MockEmptyPod {
    pub fn new_boxed(params: &Params, vd_set: VDSet) -> Box<dyn RecursivePod> {
        let statements = [mainpod::Statement::from(empty_statement())];
        let sts_hash = calculate_sts_hash(&statements, params);
        Box::new(Self {
            params: params.clone(),
            sts_hash,
            vd_set,
        })
    }
}

impl Pod for MockEmptyPod {
    fn params(&self) -> &Params {
        &self.params
    }
    fn verify(&self) -> Result<()> {
        let statements = self
            .pub_self_statements()
            .into_iter()
            .map(mainpod::Statement::from)
            .collect_vec();
        let sts_hash = calculate_sts_hash(&statements, &self.params);
        if sts_hash != self.sts_hash {
            return Err(Error::sts_hash_not_equal(self.sts_hash, sts_hash));
        }
        Ok(())
    }
    fn id(&self) -> Hash {
        self.sts_hash
    }
    fn pod_type(&self) -> (usize, &'static str) {
        (PodType::MockEmpty as usize, "MockEmpty")
    }
    fn pub_self_statements(&self) -> Vec<Statement> {
        vec![empty_statement()]
    }

    fn serialize_data(&self) -> serde_json::Value {
        serde_json::Value::Null
    }
}

impl RecursivePod for MockEmptyPod {
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
    fn deserialize_data(
        params: Params,
        _data: serde_json::Value,
        vd_set: VDSet,
        id: Hash,
    ) -> Result<Box<dyn RecursivePod>> {
        Ok(Box::new(Self {
            params,
            sts_hash: id,
            vd_set,
        }))
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn test_mock_empty_pod() {
        let params = Params::default();

        let empty_pod = MockEmptyPod::new_boxed(&params, VDSet::new(8, &[]).unwrap());
        empty_pod.verify().unwrap();
    }
}
