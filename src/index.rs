use std::hash::Hash;


/// A Tag struct is a tuple name and value
pub struct Tag<V>(&'static str, V)
where
    V: Hash + Clone + Into<V>;

/// An Index is a tuple tag and index reference
pub struct Index<V>(Tag<V>, u64)
where
    V: Hash + Clone + Into<V>;
