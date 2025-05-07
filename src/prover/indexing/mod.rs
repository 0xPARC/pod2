// src/prover/indexing/mod.rs

use std::collections::{HashMap, HashSet};
use std::hash::Hash; // Note: Removed Hasher import as it wasn't used directly

use petgraph::unionfind::UnionFind;

use crate::middleware::{
    AnchoredKey, Key, Params, PodId, Predicate, Statement, StatementArg, ToFields, Value, F, SELF,
};

/// Represents different types of concrete values that can appear as arguments
/// in statements, used as a key for indexing statements by argument.
#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub enum IndexableValue {
    AnchoredKey(AnchoredKey),
    Value(Value),
    /// Stores pre-computed fields for `WildcardValue` to ensure hashability,
    /// as the underlying `Value` might not be directly hashable in all cases.
    WildcardValueFields(Vec<F>),
    None,
}

impl IndexableValue {
    /// Creates an IndexableValue from a StatementArg, requiring Params
    /// to compute fields for `WildcardValue` variants.
    fn from_arg(arg: &StatementArg, params: &Params) -> Self {
        match arg {
            StatementArg::Key(ak) => IndexableValue::AnchoredKey(ak.clone()),
            StatementArg::Literal(v) => IndexableValue::Value(v.clone()),
            StatementArg::WildcardLiteral(wv) => {
                IndexableValue::WildcardValueFields(wv.to_fields(params))
            }
            StatementArg::None => IndexableValue::None,
        }
    }
}

/// Type alias for the canonical representative ID (a usize) used by the DSU.
type CanonicalId = usize;

/// Helper to normalize pairs of IDs for neq_set for consistent ordering.
fn normalize_pair_id(a: CanonicalId, b: CanonicalId) -> (CanonicalId, CanonicalId) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}

/// Helper to normalize pairs of AnchoredKey for tracking processed value pairs.
/// Uses the `Debug` representation for deterministic ordering because `F` doesn't implement `Ord`.
fn normalize_pair_key(a: AnchoredKey, b: AnchoredKey) -> (AnchoredKey, AnchoredKey) {
    if format!("{:?}", a) <= format!("{:?}", b) {
        (a, b)
    } else {
        (b, a)
    }
}

/// Maps Predicate (as `Vec<F>`) -> argument index -> argument value (as `IndexableValue`)
/// to a set of `(PodId, Statement)` that have that argument value at that position.
type PredicateArgumentMap =
    HashMap<Vec<F>, HashMap<usize, HashMap<IndexableValue, HashSet<(PodId, Statement)>>>>;

/// Contains various indexes over prover facts (Statements) to accelerate lookups
/// during the constraint solving phase.
pub struct ProverIndexes {
    pub params: Params,
    /// Direct lookup from AnchoredKey to its concrete Value (from ValueOf statements).
    pub value_map: HashMap<AnchoredKey, Value>,

    // DSU related fields for tracking equality sets.
    /// Disjoint Set Union structure tracking equivalence classes of AnchoredKeys via usize IDs.
    pub dsu: UnionFind<usize>,
    /// Mapping from AnchoredKey to its assigned usize ID.
    pub key_to_id: HashMap<AnchoredKey, usize>,
    /// Mapping from usize ID back to the original AnchoredKey.
    pub id_to_key: Vec<AnchoredKey>,
    /// Counter for assigning new unique IDs.
    pub next_id: usize,

    /// Stores pairs of canonical IDs known *not* to be equal,
    /// derived from `NotEqual`, `Gt`, `Lt` statements or differing `ValueOf` assignments.
    pub neq_set: HashSet<(CanonicalId, CanonicalId)>,

    /// Stores `(PodId, Statement)` for fast checking of exact statement existence.
    pub exact_statement_lookup: HashSet<(PodId, Statement)>,

    /// Maps a Key to all AnchoredKeys seen using that Key.
    pub key_to_anchored_keys: HashMap<Key, HashSet<AnchoredKey>>,

    /// Maps a PodId to all AnchoredKeys seen associated with that PodId.
    pub pod_id_to_anchored_keys: HashMap<PodId, HashSet<AnchoredKey>>,

    /// Maps Predicate (as `Vec<F>`) -> argument index -> argument value (as `IndexableValue`)
    /// to a set of `(PodId, Statement)` that have that argument value at that position.
    pub statement_lookup_by_arg: PredicateArgumentMap,
}

impl ProverIndexes {
    pub fn new(params: Params) -> Self {
        Self {
            params,
            value_map: HashMap::new(),
            dsu: UnionFind::new(0),
            key_to_id: HashMap::new(),
            id_to_key: Vec::new(),
            next_id: 0,
            neq_set: HashSet::new(),
            exact_statement_lookup: HashSet::new(),
            key_to_anchored_keys: HashMap::new(),
            pod_id_to_anchored_keys: HashMap::new(),
            statement_lookup_by_arg: HashMap::new(),
        }
    }

    /// Helper to get or assign a usize ID for an AnchoredKey, used for DSU interaction.
    fn get_or_assign_id(&mut self, ak: &AnchoredKey) -> usize {
        *self.key_to_id.entry(ak.clone()).or_insert_with(|| {
            let id = self.next_id;
            self.next_id += 1;
            self.id_to_key.push(ak.clone());
            assert_eq!(
                self.id_to_key.len() - 1,
                id,
                "Internal ID tracking mismatch"
            );
            id
        })
    }

    /// Builds all indexes from a collection of initial facts.
    /// Operates in multiple passes:
    /// 1. Assign internal IDs (`usize`) to all unique `AnchoredKey`s encountered.
    /// 2. Initialize the DSU structure with the total count of unique keys.
    /// 3. Populate all index maps (`value_map`, `key_to_anchored_keys`, etc.) and the `exact_statement_lookup` set.
    ///    Also processes explicit equalities (`Equal`) via DSU unions and explicit inequalities (`NotEqual`, `Gt`, `Lt`) by populating `neq_set`.
    /// 4. Derive implicit equalities and inequalities based on `ValueOf` statements. Keys with the same value are unioned in the DSU
    ///    (unless explicitly marked `NotEqual`), and keys with different values have their canonical IDs added to `neq_set`.
    pub fn build(params: Params, initial_facts: &[(PodId, Statement)]) -> Self {
        let mut indexes = Self::new(params);

        // Pass 1: Assign IDs to all unique AnchoredKeys encountered.
        for (_pod_id, statement) in initial_facts {
            for arg in statement.args() {
                if let StatementArg::Key(ak) = arg {
                    let _ = indexes.get_or_assign_id(&ak);
                }
            }
            // Assign ID for the AK defined BY a ValueOf statement itself
            if let Statement::ValueOf(ak, _) = statement {
                let _ = indexes.get_or_assign_id(ak);
            }
        }

        // Initialize DSU with the final count of unique keys.
        indexes.dsu = UnionFind::new(indexes.next_id);

        // Pass 2: Populate indexes using assigned IDs.
        for (pod_id, statement) in initial_facts {
            // println!("INDEXING: Processing fact: ({:?}, {:?})", pod_id, statement); // Re-enable

            // --- Temporarily comment out all processing logic within the loop --- START ---
            // Restore the commented-out logic
            indexes
                .exact_statement_lookup
                .insert((*pod_id, statement.clone()));

            // Populate key/pod lookups
            for arg in statement.args() {
                if let StatementArg::Key(ak) = arg {
                    let key_for_map = ak.key.clone();
                    let ak_set = indexes
                        .key_to_anchored_keys
                        .entry(key_for_map.clone())
                        .or_default();
                    ak_set.insert(ak.clone());
                    let ak_set_pod = indexes
                        .pod_id_to_anchored_keys
                        .entry(ak.pod_id)
                        .or_default();
                    ak_set_pod.insert(ak.clone());
                }
            }
            // Populate value_map
            if let Statement::ValueOf(ak, v) = statement {
                indexes.value_map.insert(ak.clone(), v.clone());
                // Re-enable debug for ValueOf SELF
                if ak.pod_id == SELF {
                    let key_for_map = ak.key.clone();
                    // Explicitly update maps here, even if redundant with loop below, for debugging
                    indexes
                        .key_to_anchored_keys
                        .entry(key_for_map)
                        .or_default()
                        .insert(ak.clone());
                    indexes
                        .pod_id_to_anchored_keys
                        .entry(ak.pod_id)
                        .or_default()
                        .insert(ak.clone());
                }
            }
            // Populate statement_lookup_by_arg
            let pred_fields = statement.predicate().to_fields(&indexes.params);
            let pred_map = indexes
                .statement_lookup_by_arg
                .entry(pred_fields)
                .or_default();
            for (i, arg) in statement.args().iter().enumerate() {
                let indexable_value = IndexableValue::from_arg(arg, &indexes.params);
                if !matches!(indexable_value, IndexableValue::None) {
                    let arg_map = pred_map.entry(i).or_default();
                    arg_map
                        .entry(indexable_value)
                        .or_default()
                        .insert((*pod_id, statement.clone()));
                }
            }

            // Process explicit equalities and inequalities.
            match statement {
                Statement::Equal(ak1, ak2) => {
                    let id1 = indexes.key_to_id[ak1];
                    let id2 = indexes.key_to_id[ak2];
                    indexes.dsu.union(id1, id2);
                }
                Statement::NotEqual(ak1, ak2) => {
                    let id1 = indexes.key_to_id[ak1];
                    let id2 = indexes.key_to_id[ak2];
                    let root1 = indexes.dsu.find(id1);
                    let root2 = indexes.dsu.find(id2);
                    if root1 != root2 {
                        indexes.neq_set.insert(normalize_pair_id(root1, root2));
                    }
                }
                // Statement::Gt(ak1, ak2) => {
                //     let id1 = indexes.key_to_id[ak1];
                //     let id2 = indexes.key_to_id[ak2];
                //     let root1 = indexes.dsu.find(id1);
                //     let root2 = indexes.dsu.find(id2);
                //     if root1 != root2 {
                //         indexes.neq_set.insert(normalize_pair_id(root1, root2));
                //     }
                // }
                Statement::Lt(ak1, ak2) => {
                    let id1 = indexes.key_to_id[ak1];
                    let id2 = indexes.key_to_id[ak2];
                    let root1 = indexes.dsu.find(id1);
                    let root2 = indexes.dsu.find(id2);
                    if root1 != root2 {
                        indexes.neq_set.insert(normalize_pair_id(root1, root2));
                    }
                }
                Statement::ValueOf(ak, _v) => {
                    // ValueOf already handled for value_map
                    // Ensure its AK is in the other maps (potentially redundant, but safe)
                    if ak.pod_id == SELF {
                        indexes
                            .key_to_anchored_keys
                            .entry(ak.key.clone())
                            .or_default()
                            .insert(ak.clone());
                        indexes
                            .pod_id_to_anchored_keys
                            .entry(ak.pod_id)
                            .or_default()
                            .insert(ak.clone());
                    }
                }
                _ => {}
            }
        }

        // Pass 3: Derive implicit Eq/NEq from ValueOf statements.
        // We iterate through all pairs of ValueOf facts to establish relationships.
        let value_map_clone = indexes.value_map.clone();
        let mut processed_pairs = HashSet::new();

        for (ak1, v1) in &value_map_clone {
            for (ak2, v2) in &value_map_clone {
                if ak1 == ak2 {
                    continue;
                }
                let key_pair = normalize_pair_key(ak1.clone(), ak2.clone());
                if processed_pairs.contains(&key_pair) {
                    continue;
                }

                let id1 = indexes.key_to_id[ak1];
                let id2 = indexes.key_to_id[ak2];
                if v1 == v2 {
                    // If values are equal, union them in the DSU, but only if
                    // they aren't already known to be explicitly unequal.
                    let root1 = indexes.dsu.find(id1);
                    let root2 = indexes.dsu.find(id2);
                    if !indexes.neq_set.contains(&normalize_pair_id(root1, root2)) {
                        indexes.dsu.union(id1, id2);
                    }
                } else {
                    // If values differ, mark them as unequal in the neq_set,
                    // but only if the DSU doesn't already consider them equal
                    // (e.g., due to an explicit `Equal` statement processed earlier).
                    let root1 = indexes.dsu.find(id1);
                    let root2 = indexes.dsu.find(id2);
                    if root1 != root2 {
                        indexes.neq_set.insert(normalize_pair_id(root1, root2));
                    }
                }
                processed_pairs.insert(key_pair);
            }
        }

        indexes
    }

    // --- Query Methods ---

    /// Retrieves the concrete value associated with an anchored key, if known.
    pub fn get_value(&self, ak: &AnchoredKey) -> Option<&Value> {
        self.value_map.get(ak)
    }

    /// Retrieves all unique AnchoredKeys known to the indexer.
    pub fn get_all_known_keys(&self) -> impl Iterator<Item = &AnchoredKey> {
        self.id_to_key.iter() // Iterate over all keys assigned an ID
    }

    /// Retrieves the internal index used by the DSU for a given AnchoredKey.
    pub fn get_key_index(&self, ak: &AnchoredKey) -> Option<usize> {
        self.key_to_id.get(ak).copied()
    }

    /// Checks if two AnchoredKeys are known to be in the same equivalence class (via DSU).
    /// Returns true if they are equivalent, false otherwise.
    /// Falls back to direct equality check (`ak1 == ak2`) if one or both keys were not assigned an ID during indexing.
    pub fn are_potentially_equal(&self, ak1: &AnchoredKey, ak2: &AnchoredKey) -> bool {
        match (self.key_to_id.get(ak1), self.key_to_id.get(ak2)) {
            (Some(&id1), Some(&id2)) => self.dsu.equiv(id1, id2),
            _ => ak1 == ak2,
        }
    }

    /// Checks if two AnchoredKeys are explicitly known *not* to be equal.
    /// This checks the `neq_set` using canonical IDs from the DSU.
    /// Returns false if they are in the same DSU set (meaning they are considered equal)
    /// or if no explicit NEq relationship was derived between their sets.
    pub fn are_not_equal(&self, ak1: &AnchoredKey, ak2: &AnchoredKey) -> bool {
        match (self.key_to_id.get(ak1), self.key_to_id.get(ak2)) {
            (Some(&id1), Some(&id2)) => {
                let root1 = self.dsu.find(id1);
                let root2 = self.dsu.find(id2);
                if root1 == root2 {
                    // If DSU says they are equivalent, they cannot be unequal.
                    false
                } else {
                    // Otherwise, check if an explicit NotEqual relationship exists in neq_set.
                    self.neq_set.contains(&normalize_pair_id(root1, root2))
                }
            }
            // Cannot determine inequality if one or both keys weren't indexed.
            _ => false,
        }
    }

    /// Checks if a specific statement exists in the initial facts.
    pub fn get_exact_statement(&self, pod_id: &PodId, statement: &Statement) -> bool {
        self.exact_statement_lookup
            .contains(&(*pod_id, statement.clone()))
    }

    /// Gets all AnchoredKeys associated with a specific Key.
    pub fn get_anchored_keys_for_key(&self, key: &Key) -> Option<&HashSet<AnchoredKey>> {
        self.key_to_anchored_keys.get(key)
    }

    /// Gets all AnchoredKeys associated with a specific PodId.
    pub fn get_anchored_keys_for_pod_id(&self, pod_id: &PodId) -> Option<&HashSet<AnchoredKey>> {
        self.pod_id_to_anchored_keys.get(pod_id)
    }

    /// Looks up potential source statements based on a specific argument value.
    /// Takes the predicate, argument index, and the *actual* argument (`StatementArg`),
    /// converts the argument to `IndexableValue` internally for lookup.
    /// Returns a set of `(PodId, Statement)` matching the criteria, allowing the caller
    /// to use the convenient `StatementArg` type directly.
    pub fn lookup_statements_by_arg(
        &self,
        predicate: &Predicate,
        arg_index: usize,
        arg_value: &StatementArg,
    ) -> Option<&HashSet<(PodId, Statement)>> {
        let pred_fields = predicate.to_fields(&self.params);
        let lookup_key = IndexableValue::from_arg(arg_value, &self.params);
        self.statement_lookup_by_arg
            .get(&pred_fields)
            .and_then(|arg_map| arg_map.get(&arg_index))
            .and_then(|value_map| value_map.get(&lookup_key))
    }

    // --- Public Getter Methods ---

    pub fn value_map(&self) -> &HashMap<AnchoredKey, Value> {
        &self.value_map
    }

    pub fn key_to_anchored_keys(&self) -> &HashMap<Key, HashSet<AnchoredKey>> {
        &self.key_to_anchored_keys
    }

    pub fn pod_id_to_anchored_keys(&self) -> &HashMap<PodId, HashSet<AnchoredKey>> {
        &self.pod_id_to_anchored_keys
    }

    /// Check if two keys are known to be equal based on the DSU.
    /// Returns true if they are in the same set, false otherwise.
    /// Falls back to direct equality check (`ak1 == ak2`) if one or both keys were not indexed.
    pub fn are_equal(&self, ak1: &AnchoredKey, ak2: &AnchoredKey) -> bool {
        match (self.key_to_id.get(ak1), self.key_to_id.get(ak2)) {
            (Some(&id1), Some(&id2)) => self.dsu.equiv(id1, id2),
            _ => ak1 == ak2,
        }
    }

    /// Check if a specific concrete statement exists in the initial facts.
    pub fn contains_exact_statement(&self, pod_id: &PodId, statement: &Statement) -> bool {
        self.exact_statement_lookup
            .contains(&(*pod_id, statement.clone()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::middleware::{hash_str, Key, NativePredicate, PodId, Predicate, Statement, Value};

    // Helper to create dummy PodId
    fn pod_id(name: &str) -> PodId {
        PodId(hash_str(name))
    }

    // Helper to create AnchoredKey
    fn ak(pod_id: PodId, key: &str) -> AnchoredKey {
        AnchoredKey::new(pod_id, Key::new(key.to_string()))
    }

    // Helper for creating Value::Int
    fn int_val(val: i64) -> Value {
        Value::from(val)
    }

    // --- Basic Setup ---
    fn basic_setup() -> (Params, Vec<(PodId, Statement)>, PodId, PodId) {
        let params = Params::default();
        let pod_a = pod_id("podA");
        let pod_b = pod_id("podB");
        let facts = vec![
            (pod_a, Statement::ValueOf(ak(pod_a, "key1"), int_val(10))),
            (pod_b, Statement::ValueOf(ak(pod_b, "key1"), int_val(20))),
            (pod_a, Statement::ValueOf(ak(pod_a, "key2"), int_val(10))),
            (
                pod_b,
                Statement::Equal(ak(pod_a, "key3"), ak(pod_b, "key3")),
            ),
            (
                pod_a,
                Statement::NotEqual(ak(pod_a, "key4"), ak(pod_b, "key4")),
            ),
            (
                pod_a,
                Statement::Lt(ak(pod_a, "lt_key"), ak(pod_b, "gt_key")),
            ), // Implies NEq
        ];
        (params, facts, pod_a, pod_b)
    }

    // --- Existing Tests ---
    #[test]
    fn test_basic_indexing() {
        let (params, facts, pod_a, pod_b) = basic_setup();
        let indexes = ProverIndexes::build(params, &facts);

        // Test get_value
        assert_eq!(indexes.get_value(&ak(pod_a, "key1")), Some(&int_val(10)));
        assert_eq!(indexes.get_value(&ak(pod_b, "key1")), Some(&int_val(20)));
        assert_eq!(indexes.get_value(&ak(pod_a, "unknown_key")), None);

        // Test get_anchored_keys_for_key
        let keys_for_key1 = indexes
            .get_anchored_keys_for_key(&Key::new("key1".to_string()))
            .unwrap();
        assert!(keys_for_key1.contains(&ak(pod_a, "key1")));
        assert!(keys_for_key1.contains(&ak(pod_b, "key1")));
        assert_eq!(keys_for_key1.len(), 2);
        assert!(indexes
            .get_anchored_keys_for_key(&Key::new("unknown".to_string()))
            .is_none());

        // Test get_anchored_keys_for_pod_id
        let keys_for_pod_a = indexes.get_anchored_keys_for_pod_id(&pod_a).unwrap();
        assert!(keys_for_pod_a.contains(&ak(pod_a, "key1")));
        assert!(keys_for_pod_a.contains(&ak(pod_a, "key2")));
        assert!(keys_for_pod_a.contains(&ak(pod_a, "key3"))); // From Equal
        assert!(keys_for_pod_a.contains(&ak(pod_a, "key4"))); // From NotEqual
        assert!(keys_for_pod_a.contains(&ak(pod_a, "lt_key")));
        assert!(!keys_for_pod_a.contains(&ak(pod_b, "gt_key")));
        assert_eq!(keys_for_pod_a.len(), 5);
        assert!(indexes
            .get_anchored_keys_for_pod_id(&pod_id("unknown"))
            .is_none());
    }

    #[test]
    fn test_dsu_explicit_eq() {
        let (params, facts, pod_a, pod_b) = basic_setup();
        let indexes = ProverIndexes::build(params, &facts);
        let key_a3 = ak(pod_a, "key3");
        let key_b3 = ak(pod_b, "key3");
        assert!(indexes.are_equal(&key_a3, &key_b3));
        assert!(indexes.are_equal(&key_b3, &key_a3));
    }

    #[test]
    fn test_dsu_derived_eq() {
        let (params, facts, pod_a, pod_b) = basic_setup();
        let mut facts_mut = facts.clone();
        // Add ValueOf for pod_b key3 to make it equal to pod_a key2
        facts_mut.push((
            pod_b,
            Statement::ValueOf(ak(pod_b, "key3_derived"), int_val(10)),
        )); // Same value as pod_a, key2

        let indexes = ProverIndexes::build(params, &facts_mut);
        let key_a2 = ak(pod_a, "key2");
        let key_b3_derived = ak(pod_b, "key3_derived");

        assert!(indexes.are_equal(&key_a2, &key_b3_derived));
        assert!(indexes.are_equal(&key_b3_derived, &key_a2));

        // Check original explicit eq still holds
        assert!(indexes.are_equal(&ak(pod_a, "key3"), &ak(pod_b, "key3")));
    }

    #[test]
    fn test_neq_explicit() {
        let (params, facts, pod_a, pod_b) = basic_setup();
        let indexes = ProverIndexes::build(params, &facts);
        let key_a4 = ak(pod_a, "key4");
        let key_b4 = ak(pod_b, "key4");
        assert!(indexes.are_not_equal(&key_a4, &key_b4));
        assert!(indexes.are_not_equal(&key_b4, &key_a4));
    }

    #[test]
    fn test_neq_derived_valueof() {
        let (params, facts, pod_a, pod_b) = basic_setup();
        let indexes = ProverIndexes::build(params, &facts);
        let key_a1 = ak(pod_a, "key1"); // value 10
        let key_b1 = ak(pod_b, "key1"); // value 20
        assert!(indexes.are_not_equal(&key_a1, &key_b1));
        assert!(indexes.are_not_equal(&key_b1, &key_a1));
    }

    #[test]
    fn test_neq_derived_lt() {
        let (params, facts, pod_a, pod_b) = basic_setup();
        let indexes = ProverIndexes::build(params, &facts);
        let key_lt = ak(pod_a, "lt_key");
        let key_gt = ak(pod_b, "gt_key");
        // Lt(pod_a, lt_key, pod_b, gt_key) implies NotEqual
        assert!(indexes.are_not_equal(&key_gt, &key_lt));
        assert!(indexes.are_not_equal(&key_lt, &key_gt));
    }

    #[test]
    fn test_neq_overrides_potential_eq() {
        // Scenario: A=10, B=10, but also NotEqual(A, B) explicitly stated. NEq should win.
        let params = Params::default();
        let pod_a = pod_id("podA");
        let pod_b = pod_id("podB");
        let facts = vec![
            (pod_a, Statement::ValueOf(ak(pod_a, "key"), int_val(10))),
            (pod_b, Statement::ValueOf(ak(pod_b, "key"), int_val(10))),
            (
                pod_a,
                Statement::NotEqual(ak(pod_a, "key"), ak(pod_b, "key")),
            ),
        ];
        let indexes = ProverIndexes::build(params, &facts);
        let key_a = ak(pod_a, "key");
        let key_b = ak(pod_b, "key");

        // Explicit NEq is present and should take precedence over ValueOf-derived equality.
        assert!(indexes.are_not_equal(&key_a, &key_b));
        // The DSU `union` operation based on ValueOf happens *after* the NEq set check
        // within the same pass, so the NEq should prevent the union.
        assert!(
            !indexes.are_equal(&key_a, &key_b),
            "Explicit NEq should prevent DSU union from ValueOf"
        );
    }

    #[test]
    fn test_dsu_merge_removes_neq() {
        // Scenario: Initially NEq(A, B) derived from values, but later explicitly Equal(A, B)
        let params = Params::default();
        let pod_a = pod_id("podA");
        let pod_b = pod_id("podB");
        let facts = vec![
            (pod_a, Statement::ValueOf(ak(pod_a, "key"), int_val(10))),
            (pod_b, Statement::ValueOf(ak(pod_b, "key"), int_val(20))), // Initially NEq
            (pod_a, Statement::Equal(ak(pod_a, "key"), ak(pod_b, "key"))), // Then Equal
        ];
        let indexes = ProverIndexes::build(params, &facts);
        let key_a = ak(pod_a, "key");
        let key_b = ak(pod_b, "key");

        // DSU should have merged them due to explicit Equal
        assert!(indexes.are_equal(&key_a, &key_b));
        // Because they are equal in DSU, are_not_equal must return false
        assert!(!indexes.are_not_equal(&key_a, &key_b));
    }

    #[test]
    fn test_get_exact_statement() {
        let (params, facts, pod_a, pod_b) = basic_setup();
        let indexes = ProverIndexes::build(params.clone(), &facts);

        let stmt1 = Statement::ValueOf(ak(pod_a, "key1"), int_val(10));
        let stmt2 = Statement::Equal(ak(pod_a, "key3"), ak(pod_b, "key3"));
        let stmt_missing = Statement::ValueOf(ak(pod_a, "key_missing"), int_val(99));
        let stmt_wrong_val = Statement::ValueOf(ak(pod_a, "key1"), int_val(99));
        let stmt_wrong_pod = Statement::ValueOf(ak(pod_b, "key1"), int_val(10)); // Value is correct, but fact was for pod_a

        assert!(indexes.get_exact_statement(&pod_a, &stmt1));
        assert!(indexes.contains_exact_statement(&pod_a, &stmt1));

        assert!(indexes.get_exact_statement(&pod_b, &stmt2)); // Correct origin pod
        assert!(indexes.contains_exact_statement(&pod_b, &stmt2));
        assert!(!indexes.get_exact_statement(&pod_a, &stmt2)); // Should not exist for pod_a

        assert!(!indexes.get_exact_statement(&pod_a, &stmt_missing));
        assert!(!indexes.contains_exact_statement(&pod_a, &stmt_missing));

        assert!(!indexes.get_exact_statement(&pod_a, &stmt_wrong_val));
        assert!(!indexes.contains_exact_statement(&pod_a, &stmt_wrong_val));

        assert!(!indexes.get_exact_statement(&pod_b, &stmt_wrong_pod));
        assert!(!indexes.contains_exact_statement(&pod_b, &stmt_wrong_pod));
    }

    #[test]
    fn test_equality_unknown_keys() {
        let (params, facts, pod_a, _pod_b) = basic_setup();
        let indexes = ProverIndexes::build(params, &facts);

        let known_key = ak(pod_a, "key1");
        let unknown_key1 = ak(pod_id("unknownPod"), "unknownKey");
        let unknown_key2 = ak(pod_id("unknownPod"), "unknownKey"); // Same as unknown_key1
        let unknown_key3 = ak(pod_id("unknownPod"), "anotherUnknownKey");

        // Test are_equal
        assert!(
            !indexes.are_equal(&known_key, &unknown_key1),
            "Known vs Unknown should not be equal (unless identical)"
        );
        assert!(
            indexes.are_equal(&unknown_key1, &unknown_key2),
            "Identical unknown keys should be equal via fallback"
        );
        assert!(
            !indexes.are_equal(&unknown_key1, &unknown_key3),
            "Different unknown keys not equal via fallback"
        );

        // Test are_not_equal
        assert!(
            !indexes.are_not_equal(&known_key, &unknown_key1),
            "NEq cannot be determined for unknown keys"
        );
        assert!(
            !indexes.are_not_equal(&unknown_key1, &unknown_key2),
            "NEq cannot be determined for unknown keys"
        );
        assert!(
            !indexes.are_not_equal(&unknown_key1, &unknown_key3),
            "NEq cannot be determined for unknown keys"
        );
    }

    #[test]
    fn test_statement_lookup_by_arg() {
        let params = Params::default();
        let pod_a = pod_id("podA");
        let pod_b = pod_id("podB");
        let pod_c = pod_id("podC");

        let ak_a1 = ak(pod_a, "key1"); // Value 10
        let ak_b1 = ak(pod_b, "key1"); // Value 20
        let ak_c1 = ak(pod_c, "key1"); // Value 10 (same as A)
        let ak_b2 = ak(pod_b, "key2");

        let stmt_vo_a1 = Statement::ValueOf(ak_a1.clone(), int_val(10));
        let stmt_vo_b1 = Statement::ValueOf(ak_b1.clone(), int_val(20));
        let stmt_vo_c1 = Statement::ValueOf(ak_c1.clone(), int_val(10));
        let stmt_eq_a1_b2 = Statement::Equal(ak_a1.clone(), ak_b2.clone()); // Equal(A1, B2)
        let stmt_eq_c1_b1 = Statement::Equal(ak_c1.clone(), ak_b1.clone()); // Equal(C1, B1)
        let stmt_lt_a1_b1 = Statement::Lt(ak_a1.clone(), ak_b1.clone()); // Lt(A1, B1)

        let facts = vec![
            (pod_a, stmt_vo_a1.clone()),
            (pod_b, stmt_vo_b1.clone()),
            (pod_c, stmt_vo_c1.clone()),
            (pod_a, stmt_eq_a1_b2.clone()),
            (pod_b, stmt_eq_c1_b1.clone()),
            (pod_c, stmt_lt_a1_b1.clone()),
        ];
        let indexes = ProverIndexes::build(params.clone(), &facts);

        let pred_eq = Predicate::Native(NativePredicate::Equal);
        let pred_lt = Predicate::Native(NativePredicate::Lt);
        let pred_val = Predicate::Native(NativePredicate::ValueOf);

        // Lookup Equal where arg 0 is ak_a1
        let lookup_val_a1 = StatementArg::Key(ak_a1.clone());
        let results = indexes
            .lookup_statements_by_arg(&pred_eq, 0, &lookup_val_a1)
            .unwrap();
        assert_eq!(results.len(), 1);
        assert!(results.contains(&(pod_a, stmt_eq_a1_b2.clone())));

        // Lookup Equal where arg 1 is ak_b1
        let lookup_val_b1 = StatementArg::Key(ak_b1.clone());
        let results = indexes
            .lookup_statements_by_arg(&pred_eq, 1, &lookup_val_b1)
            .unwrap();
        assert_eq!(results.len(), 1);
        assert!(results.contains(&(pod_b, stmt_eq_c1_b1.clone())));

        // Lookup Lt where arg 0 is ak_a1
        let results = indexes
            .lookup_statements_by_arg(&pred_lt, 0, &lookup_val_a1)
            .unwrap();
        assert_eq!(results.len(), 1);
        assert!(results.contains(&(pod_c, stmt_lt_a1_b1.clone())));

        // Lookup ValueOf where arg 1 (the value) is int_val(10)
        let lookup_val_10 = StatementArg::Literal(int_val(10));
        let results = indexes
            .lookup_statements_by_arg(&pred_val, 1, &lookup_val_10)
            .unwrap();
        assert_eq!(results.len(), 2);
        assert!(results.contains(&(pod_a, stmt_vo_a1.clone())));
        assert!(results.contains(&(pod_c, stmt_vo_c1.clone())));

        // Lookup non-existent value
        let lookup_val_99 = StatementArg::Literal(int_val(99));
        assert!(indexes
            .lookup_statements_by_arg(&pred_val, 1, &lookup_val_99)
            .is_none());

        // Lookup wrong index
        assert!(indexes
            .lookup_statements_by_arg(&pred_eq, 2, &lookup_val_a1)
            .is_none()); // Equal only has 2 args (index 0, 1)

        // Lookup wrong predicate
        assert!(indexes
            .lookup_statements_by_arg(&pred_lt, 0, &lookup_val_b1)
            .is_none()); // Lt(A1, B1) exists, Lt(B1, ...) does not in the facts.
    }
}
