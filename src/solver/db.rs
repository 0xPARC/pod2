//! The FactDB is the queryable, indexed collection of all ground facts
//! asserted across the entire set of known PODs. It serves as the "Extensional
//! Database" (EDB) for the Datalog solver.
//!
//! The Interpreter queries this database to find initial facts to kick-start
//! or continue the reasoning process.

use std::collections::{HashMap, HashSet};

use petgraph::{
    algo::{astar, has_path_connecting},
    graph::{DiGraph, NodeIndex},
    visit::{Bfs, Reversed},
};

use crate::middleware::{
    self, AnchoredKey, Hash, Key, Pod, PodId, RawValue, Statement, StatementArg, Value, ValueRef,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EqualityKind {
    Transitive, // From an explicit Equal(A,B) statement
    ByValue,    // Derived from Value(A) == Value(B)
    Unknown,    // No known constraint on value type
                // We *could* add "String" here, and infer that Dictionary keys are Strings
}

#[derive(Debug)]
pub enum ValueEquivalenceClass {
    Numeric,   // Int or Bool
    Container, // Array, Set, or Dict
    Raw,       // E.g. for HashOf,
    Unknown,   // No known constraint on value type
               // We *could* add "String" here, and infer that Dictionary keys are Strings
}

/// A map from a statement's arguments to a list of PodIds that assert it.
pub type ProvenanceIndex<T> = HashMap<T, Vec<PodId>>;

#[derive(Debug, Default)]
pub struct StatementIndex {
    pub equal: ProvenanceIndex<[ValueRef; 2]>,
    pub lt: ProvenanceIndex<[ValueRef; 2]>,
    pub contains: ProvenanceIndex<[ValueRef; 3]>,
    pub not_contains: ProvenanceIndex<[ValueRef; 2]>,
    pub sum_of: ProvenanceIndex<[ValueRef; 3]>,
    pub not_equal: ProvenanceIndex<[ValueRef; 2]>,
    pub lt_eq: ProvenanceIndex<[ValueRef; 2]>,
    pub product_of: ProvenanceIndex<[ValueRef; 3]>,
    pub max_of: ProvenanceIndex<[ValueRef; 3]>,
    pub hash_of: ProvenanceIndex<[ValueRef; 3]>,
    // (custom_predicate_batch_id, index, statement_args) -> pod_ids
    pub custom: ProvenanceIndex<(Hash, usize, Vec<Value>)>,
}

impl StatementIndex {
    pub fn new() -> Self {
        Self::default()
    }
}

/// The database of ground truth facts, indexed for efficient querying.
///
/// This database stores facts using the interned `AtomId` type for performance,
/// allowing for fast joins and lookups within the solver.
#[derive(Debug, Default)]
pub struct FactDB {
    // The choice of indices is critical for performance and depends on the
    // patterns of queries the interpreter will make.
    /// Maps a Key to all AnchoredKeys seen using that Key.
    key_to_anchored_keys: HashMap<Key, HashSet<AnchoredKey>>,

    /// Maps a PodId to all AnchoredKeys seen associated with that PodId.
    pod_id_to_anchored_keys: HashMap<PodId, HashSet<AnchoredKey>>,

    /// Maps a PodId to the Pod itself.
    pod_id_to_pod: HashMap<PodId, Box<dyn Pod>>,

    pub equality_graph: EqualityGraph,

    /// Maps a RawValue to all AnchoredKeys known to have that value.
    raw_value_to_anchored_keys: HashMap<RawValue, HashSet<AnchoredKey>>,

    anchored_key_to_value: HashMap<AnchoredKey, Value>,

    anchored_key_value_type: HashMap<AnchoredKey, ValueEquivalenceClass>,

    pub statement_index: StatementIndex,
}

#[derive(Debug)]
pub struct EqualityGraph {
    graph: DiGraph<AnchoredKey, EqualityKind>, // Edge weight is now EqualityKind
    ak_to_node: HashMap<AnchoredKey, NodeIndex>,
}

impl EqualityGraph {
    pub fn new() -> Self {
        Self {
            graph: DiGraph::new(), // DiGraph::new() is fine for generic edge types
            ak_to_node: HashMap::new(),
        }
    }

    fn get_or_add_node(&mut self, ak: &AnchoredKey) -> NodeIndex {
        *self
            .ak_to_node
            .entry(ak.clone())
            .or_insert_with(|| self.graph.add_node(ak.clone()))
    }

    /// Adds an equality relationship with a specified kind.
    pub fn add_equality(&mut self, ak1: &AnchoredKey, ak2: &AnchoredKey, kind: EqualityKind) {
        let node1_idx = self.get_or_add_node(ak1);
        let node2_idx = self.get_or_add_node(ak2);
        self.graph.add_edge(node1_idx, node2_idx, kind);
    }

    /// Finds a path from `start_ak` to `end_ak` and returns the nodes in the path.
    pub fn find_path_and_nodes(
        &self,
        start_ak: &AnchoredKey,
        end_ak: &AnchoredKey,
    ) -> Option<Vec<AnchoredKey>> {
        let &start_node = self.ak_to_node.get(start_ak)?;
        let &end_node = self.ak_to_node.get(end_ak)?;

        astar(
            &self.graph,
            start_node,
            |finish| finish == end_node,
            |_| 1, // Edge cost
            |_| 0, // Heuristic
        )
        .map(|(_cost, path)| {
            path.into_iter()
                .map(|node_index| self.graph[node_index].clone())
                .collect()
        })
    }

    /// Checks if a path exists from `ak1` to `ak2`.
    pub fn find_path(&self, ak1: &AnchoredKey, ak2: &AnchoredKey) -> bool {
        if let (Some(&node1_idx), Some(&node2_idx)) =
            (self.ak_to_node.get(ak1), self.ak_to_node.get(ak2))
        {
            has_path_connecting(&self.graph, node1_idx, node2_idx, None)
        } else {
            false
        }
    }

    /// Finds all AnchoredKeys reachable from a given start node.
    pub fn find_reachable_forward(&self, start_ak: &AnchoredKey) -> HashSet<AnchoredKey> {
        let mut reachable = HashSet::new();
        if let Some(&start_node_idx) = self.ak_to_node.get(start_ak) {
            let mut bfs = Bfs::new(&self.graph, start_node_idx);
            while let Some(node_idx) = bfs.next(&self.graph) {
                if let Some(ak) = self.graph.node_weight(node_idx) {
                    reachable.insert(ak.clone());
                }
            }
        }
        reachable
    }

    /// Finds all AnchoredKeys that can reach a given end node.
    pub fn find_reachable_backward(&self, end_ak: &AnchoredKey) -> HashSet<AnchoredKey> {
        let mut reachable = HashSet::new();
        if let Some(&end_node_idx) = self.ak_to_node.get(end_ak) {
            // Use Reversed to traverse backwards
            let reversed_graph = Reversed(&self.graph);
            let mut bfs = Bfs::new(reversed_graph, end_node_idx);
            while let Some(node_idx) = bfs.next(reversed_graph) {
                if let Some(ak) = self.graph.node_weight(node_idx) {
                    reachable.insert(ak.clone());
                }
            }
        }
        reachable
    }

    /// Checks if there is a path from any of the `starts` to any of the `ends`.
    pub fn find_path_between_sets(
        &self,
        starts: &HashSet<AnchoredKey>,
        ends: &HashSet<AnchoredKey>,
    ) -> bool {
        // This is a simple but correct implementation. For higher performance with
        // large sets, a parallel BFS from both `starts` and `ends` that
        // meets in the middle would be more efficient than computing the full
        // reachable sets first.
        let mut reachable_from_starts = HashSet::new();
        for start_ak in starts {
            reachable_from_starts.extend(self.find_reachable_forward(start_ak));
        }

        // Optimization: if any of the ends are already in the reachable set, we are done.
        if !ends.is_disjoint(&reachable_from_starts) {
            return true;
        }

        let mut can_reach_ends = HashSet::new();
        for end_ak in ends {
            can_reach_ends.extend(self.find_reachable_backward(end_ak));
        }

        !reachable_from_starts.is_disjoint(&can_reach_ends)
    }
}

impl Default for EqualityGraph {
    fn default() -> Self {
        Self::new()
    }
}

impl FactDB {
    pub fn new() -> Self {
        Self {
            key_to_anchored_keys: HashMap::new(),
            pod_id_to_anchored_keys: HashMap::new(),
            pod_id_to_pod: HashMap::new(),
            equality_graph: EqualityGraph::new(),
            raw_value_to_anchored_keys: HashMap::new(),
            anchored_key_value_type: HashMap::new(),
            statement_index: StatementIndex::new(),
            anchored_key_to_value: HashMap::new(),
        }
    }

    pub fn get_pod_ids_with_key(&self, key: &Key) -> HashSet<PodId> {
        self.key_to_anchored_keys
            .get(key)
            .map(|aks| aks.iter().map(|ak| ak.pod_id).collect())
            .unwrap_or_default()
    }

    pub fn get_aks_with_key(&self, key: &Key) -> &HashSet<AnchoredKey> {
        static EMPTY_AK_SET: std::sync::OnceLock<HashSet<AnchoredKey>> = std::sync::OnceLock::new();
        self.key_to_anchored_keys
            .get(key)
            .unwrap_or_else(|| EMPTY_AK_SET.get_or_init(HashSet::new))
    }

    pub fn get_pod_ids_with_keys(&self, keys: &HashSet<Key>) -> HashSet<PodId> {
        let mut pod_ids = HashSet::new();
        for key in keys {
            if let Some(anchored_keys) = self.key_to_anchored_keys.get(key) {
                for anchored_key in anchored_keys {
                    pod_ids.insert(anchored_key.pod_id);
                }
            }
        }
        pod_ids
    }

    pub fn all_pod_ids_domain(&self) -> Vec<PodId> {
        self.pod_id_to_anchored_keys.keys().cloned().collect()
    }

    pub fn add_anchored_key(&mut self, ak: &AnchoredKey) {
        if self.key_to_anchored_keys.contains_key(&ak.key) {
            self.key_to_anchored_keys
                .get_mut(&ak.key)
                .unwrap()
                .insert(ak.clone());
        } else {
            let mut keys = HashSet::new();
            keys.insert(ak.clone());
            self.key_to_anchored_keys.insert(ak.key.clone(), keys);
        }
        if let std::collections::hash_map::Entry::Vacant(e) =
            self.pod_id_to_anchored_keys.entry(ak.pod_id)
        {
            let mut keys = HashSet::new();
            keys.insert(ak.clone());
            e.insert(keys);
        } else {
            self.pod_id_to_anchored_keys
                .get_mut(&ak.pod_id)
                .unwrap()
                .insert(ak.clone());
        }
    }

    pub fn add_value_type(&mut self, ak: &AnchoredKey, value_type: ValueEquivalenceClass) {
        self.anchored_key_value_type
            .entry(ak.clone())
            .or_insert(value_type);
    }

    pub fn build(pods: Vec<Box<dyn Pod>>) -> Result<Self, String> {
        let mut db = Self::new();
        for pod in pods {
            let pod_id = pod.id();
            db.pod_id_to_pod.insert(pod_id, pod);
        }

        // Collect all statements with their pod_id first to avoid borrow checker issues.
        let all_statements: Vec<(PodId, Statement)> = db
            .pod_id_to_pod
            .iter()
            .flat_map(|(pod_id, pod)| {
                pod.pub_statements()
                    .into_iter()
                    .map(move |stmt| (*pod_id, stmt))
            })
            .collect();

        // Second pass: process all statements from all pods, tracking provenance.
        for (pod_id, statement) in all_statements {
            // First, add any new anchored keys to the indices
            for arg in statement.args() {
                if let StatementArg::Key(ak) = arg {
                    db.add_anchored_key(&ak);
                }
            }

            // Now, index the statement itself with its PodId
            match statement {
                Statement::Equal(vr1, vr2) => {
                    db.statement_index
                        .equal
                        .entry([vr1.clone(), vr2.clone()])
                        .or_default()
                        .push(pod_id);

                    if let (ValueRef::Key(ak1), ValueRef::Key(ak2)) = (&vr1, &vr2) {
                        db.equality_graph
                            .add_equality(ak1, ak2, EqualityKind::Transitive);
                    }
                    if let (ValueRef::Key(ak), ValueRef::Literal(val))
                    | (ValueRef::Literal(val), ValueRef::Key(ak)) = (vr1, vr2)
                    {
                        db.add_value_mapping(&ak, val);
                    }
                }
                Statement::Lt(vr1, vr2) => {
                    db.statement_index
                        .lt
                        .entry([vr1, vr2])
                        .or_default()
                        .push(pod_id);
                }
                Statement::Contains(vr1, vr2, vr3) => {
                    db.statement_index
                        .contains
                        .entry([vr1, vr2, vr3])
                        .or_default()
                        .push(pod_id);
                }
                Statement::NotContains(vr1, vr2) => {
                    db.statement_index
                        .not_contains
                        .entry([vr1, vr2])
                        .or_default()
                        .push(pod_id);
                }
                Statement::SumOf(vr1, vr2, vr3) => {
                    db.statement_index
                        .sum_of
                        .entry([vr1, vr2, vr3])
                        .or_default()
                        .push(pod_id);
                }
                Statement::NotEqual(vr1, vr2) => {
                    db.statement_index
                        .not_equal
                        .entry([vr1, vr2])
                        .or_default()
                        .push(pod_id);
                }
                Statement::LtEq(vr1, vr2) => {
                    db.statement_index
                        .lt_eq
                        .entry([vr1, vr2])
                        .or_default()
                        .push(pod_id);
                }
                Statement::ProductOf(vr1, vr2, vr3) => {
                    db.statement_index
                        .product_of
                        .entry([vr1, vr2, vr3])
                        .or_default()
                        .push(pod_id);
                }
                Statement::MaxOf(vr1, vr2, vr3) => {
                    db.statement_index
                        .max_of
                        .entry([vr1, vr2, vr3])
                        .or_default()
                        .push(pod_id);
                }
                Statement::HashOf(vr1, vr2, vr3) => {
                    db.statement_index
                        .hash_of
                        .entry([vr1, vr2, vr3])
                        .or_default()
                        .push(pod_id);
                }
                Statement::Custom(cpr, wcv) => {
                    db.statement_index
                        .custom
                        .entry((cpr.batch.id(), cpr.index, wcv))
                        .or_default()
                        .push(pod_id);
                }
                _ => {} // Ignore other statement types for now
            }
        }

        // Third pass: Add ByValue equalities
        for anchored_keys_with_same_value in db.raw_value_to_anchored_keys.values() {
            if anchored_keys_with_same_value.len() > 1 {
                let aks_vec: Vec<&AnchoredKey> = anchored_keys_with_same_value.iter().collect();
                for i in 0..aks_vec.len() {
                    for j in (i + 1)..aks_vec.len() {
                        let ak1 = aks_vec[i];
                        let ak2 = aks_vec[j];
                        // Add bidirectional edges for value equality
                        db.equality_graph
                            .add_equality(ak1, ak2, EqualityKind::ByValue);
                        db.equality_graph
                            .add_equality(ak2, ak1, EqualityKind::ByValue);
                    }
                }
            }
        }

        // TODO: use equalities to propagate value type information

        Ok(db)
    }

    pub fn get_value_by_anchored_key(&self, ak: &AnchoredKey) -> Option<&Value> {
        self.anchored_key_to_value.get(ak)
    }

    pub fn get_aks_by_value(&self, value: &Value) -> Option<&HashSet<AnchoredKey>> {
        self.raw_value_to_anchored_keys.get(&value.raw())
    }

    // --- Equality Graph Methods ---

    pub fn find_equality_path(&self, start: &AnchoredKey, end: &AnchoredKey) -> bool {
        self.equality_graph.find_path(start, end)
    }

    pub fn find_reachable_forward(&self, start: &AnchoredKey) -> HashSet<AnchoredKey> {
        self.equality_graph.find_reachable_forward(start)
    }

    pub fn find_reachable_backward(&self, end: &AnchoredKey) -> HashSet<AnchoredKey> {
        self.equality_graph.find_reachable_backward(end)
    }

    pub fn find_path_between_sets(
        &self,
        starts: &HashSet<AnchoredKey>,
        ends: &HashSet<AnchoredKey>,
    ) -> bool {
        self.equality_graph.find_path_between_sets(starts, ends)
    }

    pub fn get_binary_statement_index(
        &self,
        pred: &middleware::NativePredicate,
    ) -> Option<&ProvenanceIndex<[ValueRef; 2]>> {
        match pred {
            middleware::NativePredicate::Equal => Some(&self.statement_index.equal),
            middleware::NativePredicate::NotEqual => Some(&self.statement_index.not_equal),
            middleware::NativePredicate::Lt => Some(&self.statement_index.lt),
            middleware::NativePredicate::LtEq => Some(&self.statement_index.lt_eq),
            middleware::NativePredicate::NotContains => Some(&self.statement_index.not_contains),
            _ => None,
        }
    }

    pub fn get_ternary_statement_index(
        &self,
        pred: &middleware::NativePredicate,
    ) -> Option<&ProvenanceIndex<[ValueRef; 3]>> {
        match pred {
            middleware::NativePredicate::Contains => Some(&self.statement_index.contains),
            middleware::NativePredicate::SumOf => Some(&self.statement_index.sum_of),
            middleware::NativePredicate::ProductOf => Some(&self.statement_index.product_of),
            middleware::NativePredicate::MaxOf => Some(&self.statement_index.max_of),
            middleware::NativePredicate::HashOf => Some(&self.statement_index.hash_of),
            _ => None,
        }
    }

    fn add_value_mapping(&mut self, ak: &AnchoredKey, val: Value) {
        self.anchored_key_to_value.insert(ak.clone(), val.clone());
        self.raw_value_to_anchored_keys
            .entry(val.raw())
            .or_default()
            .insert(ak.clone());
    }
}
