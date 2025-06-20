use std::{
    cell::RefCell,
    collections::{hash_map::DefaultHasher, HashSet},
    hash::{Hash, Hasher},
    sync::Arc,
};

use itertools::Itertools;

use crate::{
    middleware::{
        self, AnchoredKey, CustomPredicateRef, Params, PodId, Predicate, StatementTmplArg,
        TypedValue, Value, ValueRef,
    },
    solver::{
        db::FactDB,
        engine::semi_naive::{Bindings, Fact, FactSource, JustificationKind, Relation},
        error::SolverError,
        semantics::predicates::PredicateHandler,
    },
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MaterialiseKey {
    pub predicate: Predicate,
    pub adornment: Vec<bool>,
    pub bound_args_hash: u64,
}

impl MaterialiseKey {
    fn from(pred: &Predicate, tmpl_args: &[StatementTmplArg], bindings: &Bindings) -> Self {
        let (mut adorn, mut hasher) = (Vec::new(), DefaultHasher::new());
        for arg in tmpl_args {
            match arg {
                StatementTmplArg::Literal(v) => {
                    adorn.push(true);
                    v.raw().hash(&mut hasher);
                }
                StatementTmplArg::Wildcard(w) => {
                    if let Some(b) = bindings.get(w) {
                        adorn.push(true);
                        b.raw().hash(&mut hasher);
                    } else {
                        adorn.push(false);
                    }
                }
                StatementTmplArg::AnchoredKey(pod_wc, key) => {
                    if let Some(b) = bindings.get(pod_wc) {
                        adorn.push(true);
                        b.raw().hash(&mut hasher);
                    } else {
                        adorn.push(false);
                    }
                    key.raw().hash(&mut hasher);
                }
                StatementTmplArg::None => adorn.push(false),
            }
        }
        Self {
            predicate: pred.clone(),
            adornment: adorn,
            bound_args_hash: hasher.finish(),
        }
    }
}

pub struct Materializer {
    db: Arc<FactDB>,
    params: Params,
    materialised_keys: RefCell<HashSet<MaterialiseKey>>,
}

impl<'a> Materializer {
    pub fn new(db: Arc<FactDB>, params: &Params) -> Self {
        Self {
            db: Arc::clone(&db),
            params: params.clone(),
            materialised_keys: RefCell::new(HashSet::new()),
        }
    }

    pub fn value_ref_to_value(&self, vr: &ValueRef) -> Option<Value> {
        self.db.value_ref_to_value(vr)
    }

    fn resolve_term(&self, arg: &StatementTmplArg, bindings: &Bindings) -> Option<Value> {
        match arg {
            StatementTmplArg::Literal(v) => Some(v.clone()),
            StatementTmplArg::Wildcard(w) => {
                let binding = bindings.get(w);
                binding.cloned()
            }
            StatementTmplArg::AnchoredKey(pod_wc, key) => {
                let binding = bindings.get(pod_wc);
                if let Some(v) = binding {
                    if let TypedValue::PodId(pod_id) = v.typed() {
                        let ak = middleware::AnchoredKey::new(*pod_id, key.clone());
                        self.db.get_value_by_anchored_key(&ak).cloned()
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            StatementTmplArg::None => None,
        }
    }

    /// Provides a generic way to iterate over all known EDB facts for a custom
    /// predicate, with optional bindings for each argument.
    pub fn iter_custom_statements(
        &'a self,
        cpr: &'a CustomPredicateRef,
        binding_vector: &'a [Option<Value>],
    ) -> impl Iterator<Item = (Vec<Value>, JustificationKind)> + 'a {
        self.db
            .statement_index
            .custom
            .iter()
            .filter(move |((batch_id, pred_idx, _), _)| {
                *batch_id == cpr.batch.id() && *pred_idx == cpr.index
            })
            .map(|((_, _, values), _)| values.clone())
            .filter(move |values| {
                binding_vector
                    .iter()
                    .zip(values.iter())
                    // If we have a binding, it must match the value. If we don't,
                    // then any value is acceptable.
                    .all(|(filter, value)| filter.as_ref().is_none_or(|f| f == value))
            })
            .map(|vals| (vals, JustificationKind::Existing))
    }

    fn column_choices(
        &self,
        arg_tmpl: &StatementTmplArg,
        binding: &Option<Value>,
    ) -> Vec<Option<ValueRef>> {
        match arg_tmpl {
            // 1. Literal --------------------------------------------------------
            StatementTmplArg::Literal(v) => vec![Some(ValueRef::Literal(v.clone()))],

            // 2. Wildcard -------------------------------------------------------
            StatementTmplArg::Wildcard(_) => match binding {
                Some(v) => vec![Some(ValueRef::Literal(v.clone()))], // bound
                None => vec![None],                                  // still free
            },

            // 3. AnchoredKey ----------------------------------------------------
            StatementTmplArg::AnchoredKey(_, key) => match binding {
                // pod already bound
                Some(v) => match PodId::try_from(v.typed()) {
                    Ok(pid) => vec![Some(ValueRef::Key(AnchoredKey::new(pid, key.clone())))],
                    Err(_) => vec![], // binding can't be a PodId
                },

                // pod unbound – enumerate every pod that has that key
                None => self
                    .db
                    .get_pod_ids_with_key(key)
                    .into_iter()
                    .map(|pid| Some(ValueRef::Key(AnchoredKey::new(pid, key.clone()))))
                    .collect(),
            },

            _ => unreachable!("None args are not allowed in statement templates"),
        }
    }

    pub fn candidate_statement_args_from_bindings(
        &self,
        args: &[StatementTmplArg],
        binds: &[Option<Value>], // binding_vector
    ) -> impl Iterator<Item = Vec<Option<ValueRef>>> + 'a {
        // build per-slot choice lists
        args.iter()
            .zip(binds)
            .map(|(arg, bind)| self.column_choices(arg, bind))
            .collect::<Vec<_>>()
            .into_iter()
            .multi_cartesian_product()
    }

    pub fn facts_for_predicate(
        &self,
        predicate: Predicate,
        args: Vec<StatementTmplArg>,
        bindings: &Bindings,
    ) -> Result<Relation, SolverError> {
        // Ok, so.
        // We have a statement template, and some bindings.
        // Maybe not complete bindings.
        // For a custom statement template, this gives us a Vec of Values.
        // For a native statement template, we could have a Vec of ValueRefs?

        // For the native statements, we want to materialize a Vec<ValueRef>
        // It must be made of ValueRefs because some of what comes back might be
        // anchored keys, not plain values (though we do know the values in many cases).

        // Because the bindings are incomplete, we might end up finding many facts,
        // indeed we find any that are compatible with the bindings.

        // Build filters (binding vector)

        let key = MaterialiseKey::from(&predicate, &args, bindings);
        if self.already_done(&key) {
            return Ok(Relation::new());
        }

        let binding_vector: Vec<Option<Value>> = args
            .iter()
            .map(|arg| self.resolve_term(arg, bindings))
            .collect();

        let rel: Relation = match predicate {
            Predicate::Custom(cpr) => self
                .iter_custom_statements(&cpr, &binding_vector)
                .map(|(fact_values, just_kind)| Fact {
                    source: FactSource::External(just_kind),
                    args: fact_values.into_iter().map(ValueRef::Literal).collect(),
                })
                .collect(),

            Predicate::Native(native_pred) => {
                let mut rel = Relation::new();

                // At this point, our binding vector can contain, in each slot:
                // - Nothing (None)
                // - A ValueRef resolving to an anchored key
                // - A Value
                //
                // From this, we can look up existing statements that match the pattern.
                // For example, Equal(?a["foo"], ?b["bar"]) will match a statement which
                // has those keys in those positions. If ?a and ?b are unbound, then we
                // will find all such statements. After doing so, we need to check that
                // the statements are true! If values for both anchored keys are known,
                // then we can do a value comparison. If not, then we can try other
                // strategies:
                // - If a matching statement exists in the DB, we can copy it
                // - For Equal, we can also attempt to construct a transitive equality
                //   path

                let candidate_args_iter =
                    self.candidate_statement_args_from_bindings(&args, &binding_vector);

                // Ok, now we have our candidate args. We need to dispatch to the handler.
                let handler = PredicateHandler::for_native_predicate(native_pred);

                for candidate_args in candidate_args_iter {
                    let new_rel = handler.materialize(&candidate_args, &self.db);
                    rel.extend(new_rel);
                }

                rel
            }
            Predicate::BatchSelf(_) => {
                unimplemented!("BatchSelf is not implemented")
            }
        };

        Ok(rel)
    }

    pub fn begin_iteration(&self) {
        self.materialised_keys.borrow_mut().clear();
    }
    pub fn already_done(&self, k: &MaterialiseKey) -> bool {
        !self.materialised_keys.borrow_mut().insert(k.clone())
    }
}
