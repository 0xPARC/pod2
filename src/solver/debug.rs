use crate::{
    middleware::{Predicate, TypedValue, Value, ValueRef},
    solver::{
        engine::semi_naive::{FactStore, ProvenanceStore},
        ir::PredicateIdentifier,
    },
};

pub fn print_all_facts(facts: &FactStore) {
    for (predicate, relation) in facts {
        let pred_name = match predicate {
            PredicateIdentifier::Normal(Predicate::Custom(cpr)) => cpr.predicate().name.clone(),
            PredicateIdentifier::Normal(Predicate::Native(native)) => {
                format!("{:?}", native)
            }
            PredicateIdentifier::Magic {
                name,
                bound_indices: _,
            } => format!("magic[{}]", name),
            PredicateIdentifier::Normal(Predicate::BatchSelf(batch_self)) => {
                format!("batch_self[{}]", batch_self)
            }
        };

        for fact in relation {
            println!(
                "{} [{}] ({:?})",
                pred_name,
                fact.args
                    .iter()
                    .map(arg_to_string)
                    .collect::<Vec<_>>()
                    .join(", "),
                fact.source
            );
        }
    }
}

pub fn print_provenance(provenance: &ProvenanceStore) {
    for ((predicate, args), (rule, bindings)) in provenance {
        println!(
            "{:?}",
            match predicate {
                PredicateIdentifier::Normal(Predicate::Custom(cpr)) => cpr.predicate().name.clone(),
                PredicateIdentifier::Normal(Predicate::Native(native)) => {
                    format!("{:?}", native)
                }
                PredicateIdentifier::Magic {
                    name,
                    bound_indices: _,
                } => format!("magic[{}]", name),
                PredicateIdentifier::Normal(Predicate::BatchSelf(batch_self)) => {
                    format!("batch_self[{}]", batch_self)
                }
            }
        );
        println!("  args: {:?}", args);
        //  println!("  rule: {:?}", rule);
        println!("  bindings: {:?}", bindings);
        println!();
    }
}

fn arg_to_string(arg: &ValueRef) -> String {
    match arg {
        ValueRef::Literal(v) => format_value(v),
        ValueRef::Key(ak) => format!("{}[\"{}\"]", ak.pod_id, ak.key.name()),
    }
}

fn format_value(v: &Value) -> String {
    match &v.typed() {
        &TypedValue::String(s) => s.clone(),
        _ => format!("{:?}", v),
    }
}
