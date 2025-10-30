pub mod algorithms;
pub mod graph;

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("the given vertex does not exist")]
    NoVertex,
    #[error("this algorithm only works on directed graphs")]
    OnlyDirected,
}
