#![allow(unused)]
use std::sync::Arc;

use crate::middleware::{
    hash_str, CustomPredicate, CustomPredicateBatch, Hash, HashOrWildcard, NativePredicate,
    Predicate, StatementTmpl, StatementTmplArg, ToFields, Value, F,
};

/// Argument to an statement template
enum HashOrWildcardStr {
    Hash(Hash), // represents a literal
    Wildcard(String),
}

/// helper to build a literal HashOrWildcardStr::Hash from the given str
fn literal(s: &str) -> HashOrWildcardStr {
    HashOrWildcardStr::Hash(hash_str(s))
}

/// helper to build a HashOrWildcardStr::Wildcard from the given str
fn wildcard(s: &str) -> HashOrWildcardStr {
    HashOrWildcardStr::Wildcard(s.to_string())
}

/// Builder Argument for the StatementTmplBuilder
enum BuilderArg {
    Literal(Value),
    /// Key: (origin, key), where origin & key can be both Hash or Wildcard
    Key(HashOrWildcardStr, HashOrWildcardStr),
}

impl From<(HashOrWildcardStr, HashOrWildcardStr)> for BuilderArg {
    fn from((pod_id, key): (HashOrWildcardStr, HashOrWildcardStr)) -> Self {
        Self::Key(pod_id, key)
    }
}

impl<V> From<V> for BuilderArg
where
    V: Into<Value>,
{
    fn from(v: V) -> Self {
        Self::Literal(v.into())
    }
}

struct StatementTmplBuilder {
    predicate: Predicate,
    args: Vec<BuilderArg>,
}

impl StatementTmplBuilder {
    fn new(p: impl Into<Predicate>) -> StatementTmplBuilder {
        StatementTmplBuilder {
            predicate: p.into(),
            args: Vec::new(),
        }
    }

    fn arg(mut self, a: impl Into<BuilderArg>) -> Self {
        self.args.push(a.into());
        self
    }
}

struct CustomPredicateBatchBuilder {
    name: String,
    predicates: Vec<CustomPredicate>,
}

impl CustomPredicateBatchBuilder {
    fn new(name: String) -> Self {
        Self {
            name,
            predicates: Vec::new(),
        }
    }

    fn predicate_and(
        &mut self,
        args: &[&str],
        priv_args: &[&str],
        sts: &[StatementTmplBuilder],
    ) -> Predicate {
        self.predicate(true, args, priv_args, sts)
    }

    fn predicate_or(
        &mut self,
        args: &[&str],
        priv_args: &[&str],
        sts: &[StatementTmplBuilder],
    ) -> Predicate {
        self.predicate(false, args, priv_args, sts)
    }

    /// creates the custom predicate from the given input, adds it to the
    /// self.predicates, and returns the index of the created predicate
    fn predicate(
        &mut self,
        conjunction: bool,
        args: &[&str],
        priv_args: &[&str],
        sts: &[StatementTmplBuilder],
    ) -> Predicate {
        let statements = sts
            .iter()
            .map(|sb| {
                let args = sb
                    .args
                    .iter()
                    .map(|a| match a {
                        BuilderArg::Literal(v) => StatementTmplArg::Literal(*v),
                        BuilderArg::Key(pod_id, key) => StatementTmplArg::Key(
                            resolve_wildcard(args, priv_args, pod_id),
                            resolve_wildcard(args, priv_args, key),
                        ),
                    })
                    .collect();
                StatementTmpl(sb.predicate.clone(), args)
            })
            .collect();
        let custom_predicate = CustomPredicate {
            conjunction,
            statements,
            args_len: args.len(),
        };
        self.predicates.push(custom_predicate);
        Predicate::BatchSelf(self.predicates.len() - 1)
    }

    fn finish(self) -> Arc<CustomPredicateBatch> {
        Arc::new(CustomPredicateBatch {
            name: self.name,
            predicates: self.predicates,
        })
    }
}

fn resolve_wildcard(args: &[&str], priv_args: &[&str], v: &HashOrWildcardStr) -> HashOrWildcard {
    match v {
        HashOrWildcardStr::Hash(h) => HashOrWildcard::Hash(*h),
        HashOrWildcardStr::Wildcard(s) => HashOrWildcard::Wildcard(
            args.iter()
                .chain(priv_args.iter())
                .enumerate()
                .find_map(|(i, name)| (&s == name).then_some(i))
                .unwrap(),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::middleware::PodType;

    #[test]
    fn test_custom_pred() {
        use NativePredicate as NP;
        use StatementTmplBuilder as STB;

        let mut builder = CustomPredicateBatchBuilder::new("eth_friend".into());
        let _eth_friend = builder.predicate_and(
            // arguments:
            &["src_or", "src_key", "dst_or", "dst_key"],
            // private arguments:
            &["attestation_pod"],
            // statement templates:
            &[
                // there is an attestation pod that's a SignedPod
                STB::new(NP::ValueOf)
                    .arg((wildcard("attestation_pod"), literal("type")))
                    .arg(PodType::Signed),
                // the attestation pod is signed by (src_or, src_key)
                STB::new(NP::Equal)
                    .arg((wildcard("attestation_pod"), literal("signer")))
                    .arg((wildcard("src_or"), wildcard("src_key"))),
                // that same attestation pod has an "attestation"
                STB::new(NP::Equal)
                    .arg((wildcard("attestation_pod"), literal("attestation")))
                    .arg((wildcard("dst_or"), wildcard("dst_key"))),
            ],
        );

        println!("a.0. eth_friend = {}", builder.predicates.last().unwrap());
        let eth_friend = builder.finish();
        // This batch only has 1 predicate, so we pick it already for convenience
        let eth_friend = Predicate::Custom(eth_friend, 0);

        // next chunk builds:
        // eth_dos_distance_base(src_or, src_key, dst_or, dst_key, distance_or, distance_key) = and<
        //   eq(src_or, src_key, dst_or, dst_key),
        //   ValueOf(distance_or, distance_key, 0)
        // >
        let mut builder = CustomPredicateBatchBuilder::new("eth_dos_distance_base".into());
        let eth_dos_distance_base = builder.predicate_and(
            &[
                // arguments:
                "src_or",
                "src_key",
                "dst_or",
                "dst_key",
                "distance_or",
                "distance_key",
            ],
            &[  // private arguments:
            ],
            &[
                // statement templates:
                STB::new(NP::Equal)
                    .arg((wildcard("src_or"), literal("src_key")))
                    .arg((wildcard("dst_or"), wildcard("dst_key"))),
                STB::new(NP::ValueOf)
                    .arg((wildcard("distance_or"), wildcard("distance_key")))
                    .arg(0),
            ],
        );
        println!(
            "b.0. eth_dos_distance_base = {}",
            builder.predicates.last().unwrap()
        );

        let eth_dos_distance = Predicate::BatchSelf(3);

        // next chunk builds:
        // eth_dos_distance_ind_0(src_or, src_key, dst_or, dst_key, distance_or, distance_key) = and<
        //   eth_dos_distance(src_or, src_key, intermed_or, intermed_key, shorter_distance_or, shorter_distance_key)

        //   // distance == shorter_distance + 1
        //   ValueOf(one_or, one_key, 1)
        //   SumOf(distance_or, distance_key, shorter_distance_or, shorter_distance_key, one_or, one_key)

        //   // intermed is a friend of dst
        //   eth_friend(intermed_or, intermed_key, dst_or, dst_key)
        // >
        let eth_dos_distance_ind = builder.predicate_and(
            &[
                // arguments:
                "src_or",
                "src_key",
                "dst_or",
                "dst_key",
                "distance_or",
                "distance_key",
            ],
            &[
                // private arguments:
                "one_or",
                "one_key",
                "shorter_distance_or",
                "shorter_distance_key",
                "intermed_or",
                "intermed_key",
            ],
            &[
                // statement templates:
                STB::new(eth_dos_distance)
                    .arg((wildcard("src_or"), wildcard("src_key")))
                    .arg((wildcard("intermed_or"), wildcard("intermed_key")))
                    .arg((
                        wildcard("shorter_distance_or"),
                        wildcard("shorter_distance_key"),
                    )),
                // distance == shorter_distance + 1
                STB::new(NP::ValueOf)
                    .arg((wildcard("one_or"), wildcard("one_key")))
                    .arg(1),
                STB::new(NP::SumOf)
                    .arg((wildcard("distance_or"), wildcard("distance_key")))
                    .arg((
                        wildcard("shorter_distance_or"),
                        wildcard("shorter_distance_key"),
                    ))
                    .arg((wildcard("one_or"), wildcard("one_key"))),
                // intermed is a friend of dst
                STB::new(eth_friend)
                    .arg((wildcard("intermed_or"), wildcard("intermed_key")))
                    .arg((wildcard("dst_or"), wildcard("dst_key"))),
            ],
        );

        println!(
            "b.1. eth_dos_distance_ind = {}",
            builder.predicates.last().unwrap()
        );

        let _eth_dos_distance = builder.predicate_or(
            &[
                "src_or",
                "src_key",
                "dst_or",
                "dst_key",
                "distance_or",
                "distance_key",
            ],
            &[],
            &[
                STB::new(eth_dos_distance_base)
                    .arg((wildcard("src_or"), wildcard("src_key")))
                    .arg((wildcard("dst_or"), wildcard("dst_key")))
                    .arg((wildcard("distance_or"), wildcard("distance_key"))),
                STB::new(eth_dos_distance_ind)
                    .arg((wildcard("src_or"), wildcard("src_key")))
                    .arg((wildcard("dst_or"), wildcard("dst_key")))
                    .arg((wildcard("distance_or"), wildcard("distance_key"))),
            ],
        );

        println!(
            "b.2. eth_dos_distance = {}",
            builder.predicates.last().unwrap()
        );
    }
}
