/// Type used to represent edge weights.
pub type Weight = u64;

pub struct AdjacencyMatrix<const V: usize>([[Option<Weight>; V]; V]);

impl<const V: usize> AdjacencyMatrix<V> {
    /// Return an immutable reference to the inner matrix.
    pub fn inner(&self) -> &[[Option<Weight>; V]; V] {
        &self.0
    }

    /// Return a mutable reference to the inner matrix.
    pub fn inner_mut(&mut self) -> &mut [[Option<Weight>; V]; V] {
        &mut self.0
    }
}

impl<const V: usize> Default for AdjacencyMatrix<V> {
    fn default() -> Self {
        Self([[None; V]; V])
    }
}
