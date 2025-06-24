use std::any::Any;

use itertools::Itertools;

use crate::{
    backends::plonky2::{
        basetypes::{Proof, VerifierOnlyCircuitData},
        error::{Error, Result},
        mainpod::{self, calculate_id},
    },
    middleware::{
        AnchoredKey, Params, Pod, PodId, PodType, RecursivePod, Statement, VDSet, Value, KEY_TYPE,
        SELF,
    },
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MockEmptyPod {
    params: Params,
    id: PodId,
    vd_set: VDSet,
}

fn type_statement() -> Statement {
    Statement::equal(
        AnchoredKey::from((SELF, KEY_TYPE)),
        Value::from(PodType::Empty),
    )
}

impl MockEmptyPod {
    pub fn new_boxed(params: &Params, vd_set: VDSet) -> Box<dyn RecursivePod> {
        let statements = [mainpod::Statement::from(type_statement())];
        let id = PodId(calculate_id(&statements, params));
        Box::new(Self {
            params: params.clone(),
            id,
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
        let id = PodId(calculate_id(&statements, &self.params));
        if id != self.id {
            return Err(Error::id_not_equal(self.id, id));
        }
        Ok(())
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

    fn as_any(&self) -> &dyn Any {
        self
    }
    fn equals(&self, other: &dyn Pod) -> bool {
        if let Some(other) = other.as_any().downcast_ref::<MockEmptyPod>() {
            self == other
        } else {
            false
        }
    }
}

impl RecursivePod for MockEmptyPod {
    fn verifier_data(&self) -> VerifierOnlyCircuitData {
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
        id: PodId,
    ) -> Result<Box<dyn RecursivePod>> {
        Ok(Box::new(Self { params, id, vd_set }))
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
