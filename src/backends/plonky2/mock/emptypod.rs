use itertools::Itertools;

use crate::{
    backends::plonky2::{
        basetypes::{Proof, VerifierOnlyCircuitData},
        error::{Error, Result},
        mainpod::{self, calculate_id},
    },
    middleware::{
        AnchoredKey, DynError, Hash, Params, Pod, PodId, PodType, RecursivePod, Statement, Value,
        KEY_TYPE, SELF,
    },
};

#[derive(Clone, Debug)]
pub struct MockEmptyPod {
    params: Params,
    id: PodId,
}

fn type_statement() -> Statement {
    Statement::equal(
        AnchoredKey::from((SELF, KEY_TYPE)),
        Value::from(PodType::Empty),
    )
}

impl MockEmptyPod {
    pub fn new_boxed(params: &Params) -> Box<dyn RecursivePod> {
        let statements = [mainpod::Statement::from(type_statement())];
        let id = PodId(calculate_id(&statements, params));
        Box::new(Self {
            params: params.clone(),
            id,
        })
    }
    fn _verify(&self) -> Result<()> {
        let statements = self
            .pub_self_statements()
            .into_iter()
            .map(mainpod::Statement::from)
            .collect_vec();
        let id = PodId(calculate_id(&statements, &self.params));
        if id != self.id {
            return Err(Error::id_not_equal(self.id, id));
        }
        Ok(())
    }
    pub(crate) fn deserialize(
        params: Params,
        id: PodId,
        _vds_root: Hash,
        _data: serde_json::Value,
    ) -> Result<Box<dyn RecursivePod>> {
        Ok(Box::new(Self { params, id }))
    }
}

impl Pod for MockEmptyPod {
    fn params(&self) -> &Params {
        &self.params
    }
    fn verify(&self) -> Result<(), Box<DynError>> {
        Ok(self._verify()?)
    }
    fn id(&self) -> PodId {
        self.id
    }
    fn pod_type(&self) -> (usize, &'static str) {
        (PodType::MockEmpty as usize, "MockEmpty")
    }
    fn pub_self_statements(&self) -> Vec<Statement> {
        vec![type_statement()]
    }

    fn serialize_data(&self) -> serde_json::Value {
        serde_json::Value::Null
    }
}

impl RecursivePod for MockEmptyPod {
    fn verifier_data(&self) -> VerifierOnlyCircuitData {
        panic!("MockEmptyPod can't be verified in a recursive MainPod circuit");
    }
    fn proof(&self) -> Proof {
        panic!("MockEmptyPod can't be verified in a recursive MainPod circuit");
    }
    fn vds_root(&self) -> Hash {
        panic!("MockEmptyPod can't be verified in a recursive MainPod circuit");
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn test_mock_empty_pod() {
        let params = Params::default();

        let empty_pod = MockEmptyPod::new_boxed(&params);
        empty_pod.verify().unwrap();
    }
}
