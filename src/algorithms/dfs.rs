use std::collections::HashSet;

use crate::Error;
use crate::graph::{Graph, Vertex};

/// Search for a vertex in `root`'s sub-graph that satisfies `f` using the
/// depth-first search algorithm.
///
/// NOTE: `f` is taken as a reference to avoid recursion limit issues during
/// code generation.
pub fn search<const V: usize, T>(
    graph: &Graph<V, T>,
    v: Vertex,
    f: &impl Fn(&T) -> bool,
    seen: &mut HashSet<Vertex>,
) -> Result<Option<Vertex>, Error> {
    graph.check_vertex(v)?;
    seen.insert(v);
    let value = graph.get_vertex(v)?;
    if f(&value) {
        return Ok(Some(v));
    }
    for u in 0..V {
        if !seen.contains(&u) && graph.has_edge(v, u)? {
            if let Some(v) = search(graph, u, f, seen)? {
                return Ok(Some(v));
            }
        }
    }
    Ok(None)
}

/// Detect cycles in a graph using a simple algorithm based on recursive DFS.
pub fn cycle_detection<const V: usize, T>(
    graph: &Graph<V, T>,
    v: Vertex,
    subtree: &mut HashSet<Vertex>,
) -> Result<bool, Error> {
    if !graph.directed {
        return Err(Error::OnlyDirected);
    }
    if subtree.contains(&v) {
        return Ok(true);
    }
    subtree.insert(v);
    for u in 0..V {
        if graph.has_edge(v, u)? {
            if cycle_detection(graph, u, subtree)? {
                return Ok(true);
            }
        }
    }
    subtree.remove(&v);
    Ok(false)
}

#[cfg(test)]
mod tests {
    use std::convert::identity;

    use super::*;

    #[test]
    fn test_search() {
        let mut graph: Graph<5, _> = Graph::undirected(std::array::from_fn(|i| 100 + i));
        graph.connect(0, 1).unwrap();
        graph.connect(0, 2).unwrap();
        graph.connect(1, 2).unwrap();
        graph.connect(2, 0).unwrap();

        // Search for a value that is not in the graph.
        assert!(search(&graph, 0, &|value| *value == 1, &mut HashSet::new()).unwrap().is_none());

        // Search for a value that is not in vertex 0's sub-graph.
        assert!(search(&graph, 0, &|value| *value == 103, &mut HashSet::new()).unwrap().is_none());

        // Search for vertex 0's value.
        assert_eq!(search(&graph, 0, &|value| *value == 100, &mut HashSet::new()).unwrap(), Some(0));

        // Search for a value that *is* in vertex 0's sub-graph.
        assert_eq!(search(&graph, 0, &|value| *value == 102, &mut HashSet::new()).unwrap(), Some(2));
    }

    #[test]
    fn test_cycle_detection() {
        let mut cyclic: Graph<5, _> = Graph::directed(std::array::from_fn(identity));
        cyclic.connect(0, 1).unwrap();
        cyclic.connect(0, 2).unwrap();
        cyclic.connect(1, 2).unwrap();
        cyclic.connect(2, 0).unwrap();

        assert!(cycle_detection(&cyclic, 0, &mut HashSet::new()).unwrap());

        let mut acyclic: Graph<5, _> = Graph::directed(std::array::from_fn(identity));
        acyclic.connect(0, 1).unwrap();
        acyclic.connect(0, 2).unwrap();
        acyclic.connect(1, 2).unwrap();
        acyclic.connect(1, 3).unwrap();
        acyclic.connect(2, 3).unwrap();

        assert!(!cycle_detection(&acyclic, 0, &mut HashSet::new()).unwrap());
    }
}
