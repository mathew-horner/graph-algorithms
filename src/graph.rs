mod adjacency_matrix;

use self::adjacency_matrix::{AdjacencyMatrix, Weight};
use crate::Error;

/// Type used to represent a vertex.
pub type Vertex = usize;

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
    pub(crate) directed: bool,
}

impl<const V: usize, T> Graph<V, T> {
    /// Create a new undirected [`Graph`].
    pub fn undirected(values: [T; V]) -> Self {
        Self { values, directed: false, matrix: Default::default() }
    }

    /// Create a new directed [`Graph`].
    pub fn directed(values: [T; V]) -> Self {
        Self { values, directed: true, matrix: Default::default() }
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
    pub(crate) fn check_vertex(&self, v: Vertex) -> Result<(), Error> {
        if v >= V { Err(Error::NoVertex) } else { Ok(()) }
    }

    /// Return an error if `u` or `v` are not in the graph.
    pub(crate) fn check_vertex_pair(&self, u: Vertex, v: Vertex) -> Result<(), Error> {
        self.check_vertex(u)?;
        self.check_vertex(v)?;
        Ok(())
    }
}
