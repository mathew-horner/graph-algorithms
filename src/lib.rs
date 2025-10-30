use std::collections::{HashSet, VecDeque};

/// Type used to represent a vertex.
type Vertex = usize;

/// Type used to represent edge weights.
type Weight = u64;

/// A graph with `V` vertices.
pub struct Graph<const V: usize, T> {
    /// The values of the vertices.
    values: [T; V],

    #[rustfmt::skip]
    /// This graph is represented by a V x V adjacency matrix where `matrix[u][v]`
    /// is either:
    ///
    /// - `Some(x)` with `x` being the weight of the edge that connects `u` to `v`.
    /// - `None` if there is no edge that connects `u` to `v.`
    matrix: AdjacencyMatrix<V>,

    /// Whether or not this is a directed graph.
    directed: bool,
}

impl<const V: usize, T> Graph<V, T> {
    /// Create a new undirected [`Graph`].
    pub fn undirected(values: [T; V]) -> Self {
        Self {
            values,
            directed: false,
            matrix: Default::default(),
        }
    }

    /// Create a new directed [`Graph`].
    pub fn directed(values: [T; V]) -> Self {
        Self {
            values,
            directed: true,
            matrix: Default::default(),
        }
    }

    /// Set the value of the vertex `v`.
    pub fn set_vertex(&mut self, v: Vertex, value: T) -> Result<(), Error> {
        self.check_vertex(v)?;
        self.values[v] = value;
        Ok(())
    }

    /// Return the value of the vertex `v`.
    pub fn get_vertex(&self, v: Vertex) -> Result<&T, Error> {
        self.check_vertex(v)?;
        Ok(&self.values[v])
    }

    /// Set the weight of the edge that connects `u` to `v`.
    pub fn set_edge(&mut self, u: Vertex, v: Vertex, value: Option<Weight>) -> Result<(), Error> {
        self.check_vertex_pair(u, v)?;
        self.matrix.inner_mut()[u][v] = value;
        if !self.directed {
            self.matrix.inner_mut()[v][u] = value;
        }
        Ok(())
    }

    /// Set the weight of the edge that connects `u` to `v` to 1.
    ///
    /// This is useful if you are using the [`Graph`] as an unweighted graph.
    pub fn connect(&mut self, u: Vertex, v: Vertex) -> Result<(), Error> {
        self.set_edge(u, v, Some(1))?;
        Ok(())
    }

    /// Set the weight of the edge that connects `u` to `v` to 0.
    ///
    /// This is useful if you are using the [`Graph`] as an unweighted graph.
    pub fn disconnect(&mut self, u: Vertex, v: Vertex) -> Result<(), Error> {
        self.set_edge(u, v, Some(0))?;
        Ok(())
    }

    /// Get the weight of the edge that connects `u` to `v`.
    pub fn get_edge(&self, u: Vertex, v: Vertex) -> Result<Option<Weight>, Error> {
        self.check_vertex_pair(u, v)?;
        let weight = self.matrix.inner()[u][v];
        debug_assert_eq!(weight, self.matrix.inner()[v][u]);
        Ok(weight)
    }

    /// Check if there is an edge that connects `u` to `v`.
    pub fn has_edge(&self, u: Vertex, v: Vertex) -> Result<bool, Error> {
        self.check_vertex_pair(u, v)?;
        let mut result = self.matrix.inner()[u][v].is_some();
        if !self.directed {
            result = result || self.matrix.inner()[v][u].is_some();
        }
        Ok(result)
    }

    /// Return an error if `v` is not in the graph.
    fn check_vertex(&self, v: Vertex) -> Result<(), Error> {
        if v >= V { Err(Error::NoVertex) } else { Ok(()) }
    }

    /// Return an error if `u` or `v` are not in the graph.
    fn check_vertex_pair(&self, u: Vertex, v: Vertex) -> Result<(), Error> {
        self.check_vertex(u)?;
        self.check_vertex(v)?;
        Ok(())
    }
}

struct AdjacencyMatrix<const V: usize>([[Option<Weight>; V]; V]);

impl<const V: usize> AdjacencyMatrix<V> {
    /// Return an immutable reference to the inner matrix.
    fn inner(&self) -> &[[Option<Weight>; V]; V] {
        &self.0
    }

    /// Return a mutable reference to the inner matrix.
    fn inner_mut(&mut self) -> &mut [[Option<Weight>; V]; V] {
        &mut self.0
    }
}

impl<const V: usize> Default for AdjacencyMatrix<V> {
    fn default() -> Self {
        Self([[None; V]; V])
    }
}

/// Search for a vertex in `root`'s sub-graph that satisfies `f` using the
/// breadth-first search algorithm.
pub fn bfs<const V: usize, T>(
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

/// Search for a vertex in `root`'s sub-graph that satisfies `f` using the
/// depth-first search algorithm.
///
/// NOTE: `f` is taken as a reference to avoid recursion limit issues during
/// code generation.
pub fn dfs<const V: usize, T>(
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
            if let Some(v) = dfs(graph, u, f, seen)? {
                return Ok(Some(v));
            }
        }
    }
    Ok(None)
}

/// Detect cycles in a graph using a simple algorithm based on recursive DFS.
pub fn dfs_cycle_detection<const V: usize, T>(
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
            if dfs_cycle_detection(graph, u, subtree)? {
                return Ok(true);
            }
        }
    }
    subtree.remove(&v);
    Ok(false)
}

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("the given vertex does not exist")]
    NoVertex,
    #[error("this algorithm only works on directed graphs")]
    OnlyDirected,
}

#[cfg(test)]
mod tests {
    use std::convert::identity;

    use super::*;

    #[test]
    fn test_bfs() {
        let mut graph: Graph<5, _> = Graph::undirected(std::array::from_fn(|i| 100 + i));
        graph.connect(0, 1).unwrap();
        graph.connect(0, 2).unwrap();
        graph.connect(1, 2).unwrap();
        graph.connect(2, 0).unwrap();

        // Search for a value that is not in the graph.
        assert!(bfs(&graph, 0, |value| *value == 1).unwrap().is_none());

        // Search for a value that is not in vertex 0's sub-graph.
        assert!(bfs(&graph, 0, |value| *value == 103).unwrap().is_none());

        // Search for vertex 0's value.
        assert_eq!(bfs(&graph, 0, |value| *value == 100).unwrap(), Some(0));

        // Search for a value that *is* in vertex 0's sub-graph.
        assert_eq!(bfs(&graph, 0, |value| *value == 102).unwrap(), Some(2));
    }

    #[test]
    fn test_dfs() {
        let mut graph: Graph<5, _> = Graph::undirected(std::array::from_fn(|i| 100 + i));
        graph.connect(0, 1).unwrap();
        graph.connect(0, 2).unwrap();
        graph.connect(1, 2).unwrap();
        graph.connect(2, 0).unwrap();

        // Search for a value that is not in the graph.
        assert!(
            dfs(&graph, 0, &|value| *value == 1, &mut HashSet::new())
                .unwrap()
                .is_none()
        );

        // Search for a value that is not in vertex 0's sub-graph.
        assert!(
            dfs(&graph, 0, &|value| *value == 103, &mut HashSet::new())
                .unwrap()
                .is_none()
        );

        // Search for vertex 0's value.
        assert_eq!(
            dfs(&graph, 0, &|value| *value == 100, &mut HashSet::new()).unwrap(),
            Some(0)
        );

        // Search for a value that *is* in vertex 0's sub-graph.
        assert_eq!(
            dfs(&graph, 0, &|value| *value == 102, &mut HashSet::new()).unwrap(),
            Some(2)
        );
    }

    #[test]
    fn test_dfs_cycle_detection() {
        let mut cyclic: Graph<5, _> = Graph::directed(std::array::from_fn(identity));
        cyclic.connect(0, 1).unwrap();
        cyclic.connect(0, 2).unwrap();
        cyclic.connect(1, 2).unwrap();
        cyclic.connect(2, 0).unwrap();

        assert!(dfs_cycle_detection(&cyclic, 0, &mut HashSet::new()).unwrap());

        let mut acyclic: Graph<5, _> = Graph::directed(std::array::from_fn(identity));
        acyclic.connect(0, 1).unwrap();
        acyclic.connect(0, 2).unwrap();
        acyclic.connect(1, 2).unwrap();
        acyclic.connect(1, 3).unwrap();
        acyclic.connect(2, 3).unwrap();

        assert!(!dfs_cycle_detection(&acyclic, 0, &mut HashSet::new()).unwrap());
    }
}
