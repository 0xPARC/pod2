use std::fmt;
use std::sync::Arc;

use super::{hash_str, Hash, NativePredicate, ToFields, Value, F};

// BEGIN Custom 1b

#[derive(Debug)]
pub enum HashOrWildcard {
    Hash(Hash),
    Wildcard(usize),
}

impl fmt::Display for HashOrWildcard {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Hash(h) => write!(f, "{}", h),
            Self::Wildcard(n) => write!(f, "*{}", n),
        }
    }
}

#[derive(Debug)]
pub enum StatementTmplArg {
    None,
    Literal(Value),
    Key(HashOrWildcard, HashOrWildcard),
}

impl fmt::Display for StatementTmplArg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::None => write!(f, "none"),
            Self::Literal(v) => write!(f, "{}", v),
            Self::Key(pod_id, key) => write!(f, "({}, {})", pod_id, key),
        }
    }
}

// END

// BEGIN Custom 2

// pub enum StatementTmplArg {
//     None,
//     Literal(Value),
//     Wildcard(usize),
// }

// END

/// Statement Template for a Custom Predicate
#[derive(Debug)]
pub struct StatementTmpl(pub Predicate, pub Vec<StatementTmplArg>);

#[derive(Debug)]
pub struct CustomPredicate {
    /// true for "and", false for "or"
    pub conjunction: bool,
    pub statements: Vec<StatementTmpl>,
    pub args_len: usize,
    // TODO: Add private args length?
    // TODO: Add args type information?
}

impl ToFields for CustomPredicate {
    fn to_fields(self) -> (Vec<F>, usize) {
        todo!()
        // let f: Vec<F> = Vec::new();
        // (self.conjunction.to_f(), 1)
    }
}

impl fmt::Display for CustomPredicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "{}<", if self.conjunction { "and" } else { "or" })?;
        for st in &self.statements {
            write!(f, "  {}", st.0)?;
            for (i, arg) in st.1.iter().enumerate() {
                if i != 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", arg)?;
            }
            writeln!(f, "),")?;
        }
        write!(f, ">(")?;
        for i in 0..self.args_len {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "*{}", i)?;
        }
        writeln!(f, ")")?;
        Ok(())
    }
}

#[derive(Debug)]
pub struct CustomPredicateBatch {
    pub name: String,
    pub predicates: Vec<CustomPredicate>,
}

impl CustomPredicateBatch {
    pub fn hash(&self) -> Hash {
        // TODO
        hash_str(&format!("{:?}", self))
    }
}

#[derive(Clone, Debug)]
pub enum Predicate {
    Native(NativePredicate),
    BatchSelf(usize),
    Custom(Arc<CustomPredicateBatch>, usize),
}

impl From<NativePredicate> for Predicate {
    fn from(v: NativePredicate) -> Self {
        Self::Native(v)
    }
}

impl ToFields for Predicate {
    fn to_fields(self) -> (Vec<F>, usize) {
        match self {
            Self::Native(p) => p.to_fields(),
            Self::BatchSelf(i) => Value::from(i as i64).to_fields(),
            Self::Custom(_pb, _i) => todo!(), // TODO
        }
    }
}

impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Native(p) => write!(f, "{:?}", p),
            Self::BatchSelf(i) => write!(f, "self.{}", i),
            Self::Custom(pb, i) => write!(f, "{}.{}", pb.name, i),
        }
    }
}
