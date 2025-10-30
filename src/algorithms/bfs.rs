use std::collections::{HashSet, VecDeque};

use crate::Error;
use crate::graph::{Graph, Vertex};

/// Search for a vertex in `root`'s sub-graph that satisfies `f` using the
/// breadth-first search algorithm.
pub fn search<const V: usize, T>(
    graph: &Graph<V, T>,
    root: Vertex,
    f: impl Fn(&T) -> bool,
) -> Result<Option<Vertex>, Error> {
    graph.check_vertex(root)?;
    let mut seen = HashSet::new();
    let mut queue = VecDeque::new();
    seen.insert(root);
    queue.push_back(root);

    while let Some(v) = queue.pop_front() {
        let value = graph.get_vertex(v)?;
        if f(&value) {
            return Ok(Some(v));
        }
        for u in 0..V {
            if !seen.contains(&u) && graph.has_edge(v, u)? {
                seen.insert(u);
                queue.push_back(u);
            }
        }
    }

    Ok(None)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_search() {
        let mut graph: Graph<5, _> = Graph::undirected(std::array::from_fn(|i| 100 + i));
        graph.connect(0, 1).unwrap();
        graph.connect(0, 2).unwrap();
        graph.connect(1, 2).unwrap();
        graph.connect(2, 0).unwrap();

        // Search for a value that is not in the graph.
        assert!(search(&graph, 0, |value| *value == 1).unwrap().is_none());

        // Search for a value that is not in vertex 0's sub-graph.
        assert!(search(&graph, 0, |value| *value == 103).unwrap().is_none());

        // Search for vertex 0's value.
        assert_eq!(search(&graph, 0, |value| *value == 100).unwrap(), Some(0));

        // Search for a value that *is* in vertex 0's sub-graph.
        assert_eq!(search(&graph, 0, |value| *value == 102).unwrap(), Some(2));
    }
}
