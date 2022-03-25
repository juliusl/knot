use std::{
    collections::{BTreeSet, HashMap, HashSet},
    fmt::{Debug, Display},
    hash::{Hash, Hasher},
};

pub trait Visitor<T>
where
    T: Hash + Clone + Into<T>,
{
    /// `visit` is a function that is called on every reference
    /// if `false` is returned the walk will not continue any further
    fn visit(&self, from: &T, to: &T) -> bool;
}

/// `Guest` just implements visitor with a noop fn
pub struct Guest;

impl<T> Visitor<T> for Guest
where
    T: Hash + Clone + Into<T>,
{
    fn visit(&self, _: &T, _: &T) -> bool {
        true
    }
}

impl Default for Guest {
    fn default() -> Self {
        Self {}
    }
}

/// `Store` is a general-purpose graph of nodes that store a value of `T` and all links to to `T`
#[derive(Clone, Debug)]
pub struct Store<T>
where
    T: Hash + Clone + Into<T>,
{
    nodes: HashMap<u64, (T, HashSet<u64>)>,
    walk_unique: bool,
}

impl<T> Display for Store<T>
where
    T: Hash + Clone + Into<T> + Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut result = Ok(());
        let result = &mut result;
        self.nodes
            .iter()
            .for_each(|v| *result = write!(f, "{:?}\n", v));

        *result
    }
}

impl<T> Hash for Store<T>
where
    T: Hash + Clone + PartialOrd,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.nodes.iter().for_each(|e| {
            let (key, (value, ..)) = e;
            {
                key.hash(state);
                value.hash(state);
            }
        });
    }
}

impl<T> Default for Store<T>
where
    T: Hash + Clone,
{
    fn default() -> Self {
        Self {
            nodes: Default::default(),
            walk_unique: true,
        }
    }
}

/// This store maintains a graph structure where the value and links to the value are stored
/// The only thing required to use this store is an instance of the type being stored
/// Each entry in the graph stores the element and a HashSet of the links
/// Each entry is keyed to the hash_code evaluation of the value being stored
/// Links between nodes are stored as a XOR-Link where `link = from ^ to`
/// where `from` and `to` are keys to the node
/// In order to traverse, starting from element T with links L
/// first the hash_code of T is evaluated `hash_code(T)`
/// links are iterated and to compute the destination the xor is taken `for link in links; let destination_key = hash_code(T) ^ link;`
/// then the destination node can be retrieved via the destination_key
impl<T> Store<T>
where
    T: Hash + Clone,
{
    /// `node` adds a node to the underlying graph for `val`
    /// If val is already a node, then no changes are made
    pub fn node(&self, val: T) -> Self {
        let mut next = self.nodes.clone();

        let hash_code = Self::get_hash_code(&val);

        if !next.contains_key(&hash_code) {
            next.insert(hash_code, (val, HashSet::new()));
            Self {
                nodes: next,
                walk_unique: self.walk_unique,
            }
        } else {
            self.to_owned()
        }
    }

    /// `link_create_if_not_exists` creates the nodes in the graph if they don't exist already
    pub fn link_create_if_not_exists(&self, from: T, to: T) -> Self {
        self.node(from.clone()).node(to.clone()).link(from, to)
    }

    /// `link` creates a link between two nodes in the underlying graph
    /// if both nodes don't already exist this is a no-op
    pub fn link(&self, from: T, to: T) -> Self {
        let from_hash_code = Self::get_hash_code(&from);
        let to_hash_code = Self::get_hash_code(&to);

        let mut next = self.nodes.clone();
        let link_code = from_hash_code ^ to_hash_code;

        // Cycle
        if link_code == 0 {
            return Self {
                nodes: next,
                walk_unique: self.walk_unique,
            };
        }

        // Values must actually exist, otherwise it's a no-op
        if let (Some((v, v_links)), Some((v2, v2_links))) = (
            self.nodes.get(&from_hash_code),
            self.nodes.get(&to_hash_code),
        ) {
            let mut v_links = v_links.clone();
            let mut v2_links = v2_links.clone();

            if v_links.insert(link_code) {
                next.insert(from_hash_code, (v.clone(), v_links));
            }

            if v2_links.insert(link_code) {
                next.insert(to_hash_code, (v2.to_owned(), v2_links));
            }
        }

        Self {
            nodes: next,
            walk_unique: self.walk_unique,
        }
    }

    /// `get` returns the current state of the node of `val`
    pub fn get(&self, val: T) -> Option<&(T, HashSet<u64>)> {
        let h = &Self::get_hash_code(&val);

        self.get_at(h)
    }

    // `get_at` returns the current state of the node at `index`
    pub fn get_at(&self, index: &u64) -> Option<&(T, HashSet<u64>)> {
        self.nodes.get(index)
    }

    /// `visit` returns all of the links to the node of `val`
    pub fn visit(&self, val: T) -> Vec<(Option<T>, Option<T>)> {
        let mut visited: Vec<(Option<T>, Option<T>)> = vec![];

        if let Some((from, links)) = self.get(val.clone()) {
            let from_code = Self::get_hash_code(&val);
            links.iter().for_each(|link| {
                let to_code = link ^ from_code;

                if let Some((to, ..)) = self.nodes.get(&to_code) {
                    visited.push((Some(from.clone()), Some(to.clone())));
                }
            });
        }

        visited
    }

    /// Walks all paths starting from val
    pub fn walk<F>(
        &self,
        val: T,
        seen: &mut HashSet<T>,
        visited: &mut HashSet<(Option<T>, Option<T>)>,
        visitor: Option<&F>,
    ) where
        T: Eq,
        F: Visitor<T>,
    {
        let start = val.clone().into();

        if seen.insert(start) {
            self.visit(val).iter().for_each(|link| {
                match link {
                    (Some(from), Some(to)) => {
                        if self.walk_unique
                            && visited.contains(&(Some(to.clone()), Some(from.clone())))
                        {
                            return;
                        }

                        if visited.insert((Some(from.clone()), Some(to.clone()))) {
                            if let Some(v) = visitor {
                                if v.visit(from, to) {
                                    self.walk::<F>(to.clone(), seen, visited, visitor)
                                } else {
                                    return;
                                }
                            }
                        }
                    }
                    _ => unreachable!("visit only returns links"),
                };
            });
        }
    }

    /// Walks all paths starting from val
    /// Uses a BTreeSet to sort the values as they are visited
    pub fn walk_ordered<F>(
        &self,
        val: T,
        seen: &mut BTreeSet<T>,
        visited: &mut BTreeSet<(Option<T>, Option<T>)>,
        visitor: Option<&F>,
    ) where
        T: Ord,
        F: Visitor<T>,
    {
        let start = val.clone();

        if seen.insert(start) {
            self.visit(val).iter().for_each(|link| {
                match link {
                    (Some(from), Some(to)) => {
                        if self.walk_unique
                            && visited.contains(&(Some(to.clone()), Some(from.clone())))
                        {
                            return;
                        }

                        if visited.insert((Some(from.clone()), Some(to.clone()))) {
                            if let Some(v) = &visitor {
                                if v.visit(from, to) {
                                    self.walk_ordered::<F>(to.clone(), seen, visited, visitor)
                                } else {
                                    return;
                                }
                            }
                        }
                    }
                    _ => unreachable!("visit only returns links"),
                };
            });
        }
    }

    /// `references` returns all nodes whose references contain a reference to `val`.
    ///  If no nodes reference `val` returns `None`.
    pub fn references(&self, val: T) -> Option<Vec<T>> {
        let code = Self::get_hash_code(&val);

        let references: Vec<T> = self
            .nodes
            .iter()
            .filter_map(|f| {
                let (id, (val, references)) = f;

                let is_ref = references.iter().any(|f| f ^ code == *id);

                if is_ref {
                    Some(val.to_owned())
                } else {
                    None
                }
            })
            .collect();

        if references.len() > 0 {
            Some(references)
        } else {
            None
        }
    }

    /// `edge_edge` creates a link between two edge nodes
    pub fn edge_edge<E>(&self, from: E, to: E) -> Self
    where
        E: Into<T> + Clone,
    {
        let f: T = from.clone().into();
        let t: T = to.clone().into();
        self.node(f.clone())
            .node(t.clone())
            .link(f.clone(), t.clone())
    }

    /// `edge` adds a node that that is constructed from some type E external to the graph
    pub fn edge<E>(&self, val: E) -> Self
    where
        E: Into<T>,
    {
        self.node(val.into())
    }

    /// `edge_link` creates a link from an edge node to a store node
    pub fn edge_link<E>(&self, from: E, to: T) -> Self
    where
        E: Into<T>,
    {
        self.link(from.into(), to)
    }

    /// `new_walk_ordered` walks the graph starting from an edge node in order
    pub fn new_walk_ordered<E, F>(
        &self,
        from: E,
        visitor: Option<&F>,
    ) -> (BTreeSet<T>, BTreeSet<(Option<T>, Option<T>)>)
    where
        E: Into<T>,
        T: Ord,
        F: Visitor<T>,
    {
        let mut seen: BTreeSet<T> = BTreeSet::new();
        let mut visited: BTreeSet<(Option<T>, Option<T>)> = BTreeSet::new();

        self.walk_ordered(from.into(), &mut seen, &mut visited, visitor);

        (seen, visited)
    }

    /// `new_walk` walks the graph starting from an edge into the store
    pub fn new_walk<E, F>(
        &self,
        from: E,
        visitor: Option<&F>,
    ) -> (HashSet<T>, HashSet<(Option<T>, Option<T>)>)
    where
        E: Into<T>,
        T: Eq,
        F: Visitor<T>,
    {
        let mut seen: HashSet<T> = HashSet::new();
        let mut visited: HashSet<(Option<T>, Option<T>)> = HashSet::new();

        self.walk(from.into(), &mut seen, &mut visited, visitor);

        (seen, visited)
    }

    /// `branch` iterates through all the references of `at` and creates a link between those references and `with`
    pub fn branch<A>(&self, at: A, with: A) -> Self
    where
        A: Into<T>,
    {
        let at = at.into();
        let with = with.into();
        let next = self.clone();
        let mut next = next.node(with.clone());

        let refs = self.references(at);
        match refs {
            Some(r) => r
                .iter()
                .for_each(|r| next = next.link(r.clone(), with.clone())),
            _ => {}
        }

        next
    }

    /// `purge` removes v and references of `v`
    pub fn purge<A>(&self, v: A) -> Self
    where
        A: Into<T>,
    {
        let v = v.into();
        let id = Self::get_hash_code(&v);

        let mut next = self.nodes.clone();
        if let Some((_, refs)) = next.remove(&id) {
            for r in refs {
                let rid = r ^ id;

                if let Some((_, set)) = next.get_mut(&rid) {
                    let to_remove = HashSet::from([r]);

                    *set = set.difference(&to_remove).map(|v| *v).collect();
                }
            }
        }

        Self {
            nodes: next,
            walk_unique: self.walk_unique,
        }
    }

    /// `unlink` removes a link between a `from` and `to`
    /// if a link does not exist than this is a noop
    pub fn unlink<A>(&self, from: A, to: A) -> Self
    where
        A: Into<T>,
    {
        let from = from.into();
        let to = to.into();
        let fid = Self::get_hash_code(&from);
        let tid = Self::get_hash_code(&to);

        let lid = fid ^ tid;

        if let (Some((_, fset)), Some((_, tset))) = (self.get_at(&fid), self.get_at(&tid)) {
            let mut next = self.nodes.clone();
            let to_remove = HashSet::from([lid]);

            let fset = fset
                .difference(&to_remove)
                .map(|a| *a)
                .collect::<HashSet<u64>>();
            let tset = tset
                .difference(&to_remove)
                .map(|a| *a)
                .collect::<HashSet<u64>>();

            next.insert(fid, (from, fset));
            next.insert(tid, (to, tset));

            Self {
                nodes: next,
                walk_unique: self.walk_unique,
            }
        } else {
            self.clone()
        }
    }

    /// `update_link` adds a new link from `at` to `update` and removes a link from `at` to `current`
    pub fn update_link(&self, at: T, current: T, update: T) -> Self {
        let at2 = at.clone();

        self.link_create_if_not_exists(at, update).unlink(at2, current)
    }

    /// `prune` removes all entries from the store that do not have any references
    pub fn prune(&self) -> Self {
        let next = self.nodes.clone();

        let next = next.iter()
            .filter(|(_, (_, r))| r.len() > 0)
            .map(|(k, (v, r))| (*k, (v.clone(), r.clone())))
            .collect();

        Self {
            nodes: next,
            walk_unique: self.walk_unique
        }
    }

    fn get_hash_code(val: &T) -> u64 {
        let mut hash_code = std::collections::hash_map::DefaultHasher::default();

        val.hash(&mut hash_code);

        hash_code.finish()
    }
}

#[test]
fn test_store() {
    let store = Store::<&'static str>::default();
    let store = store
        .node("test-node-1")
        .node("test-node-2")
        .node("test-node-3")
        .node("test-node-4");
    let store = store
        .link("test-node-1", "test-node-2")
        .link("test-node-2", "test-node-1")
        .link("test-node-2", "test-node-3")
        .link("test-node-4", "test-node-3");

    // Creating store with a compact form
    let store2 = Store::<&'static str>::default()
        .link_create_if_not_exists("test-node-1", "test-node-2")
        .link_create_if_not_exists("test-node-2", "test-node-1")
        .link_create_if_not_exists("test-node-2", "test-node-3")
        .link_create_if_not_exists("test-node-4", "test-node-3");

    fn test_store_integrity(s: Store<&'static str>) {
        let visited = s.visit("test-node-1").iter().any(|v| match v {
            (Some("test-node-1"), Some("test-node-2")) => true,
            _ => false,
        });

        assert!(visited, "did not find the expected link");

        let mut seen: HashSet<&'static str> = HashSet::new();
        let mut visited: HashSet<(Option<&'static str>, Option<&'static str>)> = HashSet::new();

        let visitor = &Guest::default();

        s.walk("test-node-1", &mut seen, &mut visited, Some(visitor));

        seen.iter().for_each(|v| println!("{:?}", v));
        visited.iter().for_each(|v| println!("{:?}", v));

        let mut seen_ordered: BTreeSet<&'static str> = BTreeSet::new();
        let mut visited_ordered: BTreeSet<(Option<&'static str>, Option<&'static str>)> =
            BTreeSet::new();

        s.walk_ordered(
            "test-node-1",
            &mut seen_ordered,
            &mut visited_ordered,
            Some(visitor),
        );

        seen_ordered.iter().for_each(|v| println!("{:?}", v));
        visited_ordered.iter().for_each(|v| println!("{:?}", v));

        assert_eq!(
            s.references("test-node-3").and_then(|mut f| Some(f.sort())),
            Some(vec!["test-node-2", "test-node-4"].sort())
        );

        // Test Additional features
        // Test branch()
        let branch_test = s.branch("test-node-3", "updated-test-node-3");
        assert_eq!(
            branch_test
                .references("updated-test-node-3")
                .and_then(|mut f| Some(f.sort())),
            Some(vec!["test-node-2", "test-node-4"].sort())
        );
        println!("BranchTest:\n{}", branch_test);

        // Test purge()
        let purge_test = s
            .branch("test-node-3", "updated-test-node-3")
            .purge("test-node-3");
        assert_eq!(purge_test.references("test-node-3"), None);
        println!("PurgeTest:\n{}", purge_test);

        // Test unlink()
        let unlink_test = s.unlink("test-node-3", "test-node-2");
        assert_eq!(
            unlink_test.references("test-node-3"),
            Some(vec!["test-node-4"])
        );
        println!("UnlinkTest:\n{}", unlink_test);

        // Test update_link()
        let update_link_test = s.update_link("test-node-3", "test-node-2", "test-node-2-1");
        assert_eq!(
            update_link_test
                .references("test-node-3")
                .and_then(|mut f| Some(f.sort())),
            Some(vec!["test-node-2-1", "test-node-4"].sort())
        );
        println!("UpdateLinkTest:\n{}", update_link_test);

        // Test prune()
        let prune_test = s.update_link("test-node-3", "test-node-2", "test-node-2-1").unlink("test-node-1", "test-node-2").prune();
        assert_eq!(prune_test.get("test-node-2"), None);
        println!("PruneTest:\n{}", prune_test);
    }

    test_store_integrity(store);
    test_store_integrity(store2);
}

#[test]
fn test_edge() {
    let indexer = Store::<Indexer>::default();

    let indexer = indexer
        .node(Indexer("test".to_string(), 5))
        .edge(IndirectIndexer());

    let mut indexer = indexer
        .link(
            Indexer("test".to_string(), 5),
            Indexer("test".to_string(), 5),
        )
        .edge_link(IndirectIndexer(), Indexer("test".to_string(), 5));

    let (seen_ordered, visited_ordered) =
        indexer.new_walk_ordered(IndirectIndexer(), Some(&Printer::default()));

    assert!(seen_ordered.contains(&IndirectIndexer().into()));
    assert!(visited_ordered.contains(&(
        Some(IndirectIndexer().into()),
        Some(Indexer("test".to_string(), 5))
    )));

    // Test walk_unique setting, this changes the behavior of walking and allows back-tracking
    // for example say there is some path A -> B, setting this field to false means that during a walk 
    // A -> B and B -> A will be visited
    indexer.walk_unique = false;

    let (_, visited_ordered) =
        indexer.new_walk_ordered(IndirectIndexer(), Some(&Printer::default()));

    assert!(visited_ordered.contains(&(
        Some(IndirectIndexer().into()),
        Some(Indexer("test".to_string(), 5))
    )));
    assert!(visited_ordered.contains(&(
        Some(Indexer("test".to_string(), 5)),
        Some(IndirectIndexer().into())
    )));
}

struct IndirectIndexer();

impl Into<Indexer> for IndirectIndexer {
    fn into(self) -> Indexer {
        Indexer("test".to_string(), 0)
    }
}

#[derive(Default, Debug, Clone, Hash, PartialEq, PartialOrd, Eq, Ord)]
struct Indexer(String, u64);

#[derive(Default)]
struct Printer;

impl Visitor<Indexer> for Printer {
    fn visit(&self, from: &Indexer, to: &Indexer) -> bool {
        println!("{:?} -> {:?}", from, to);
        true
    }
}
