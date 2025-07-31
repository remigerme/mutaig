use thiserror::Error;

use crate::miter::MiterError;

use super::NodeId;

/// The result of an AIG operation.
pub type Result<T> = std::result::Result<T, AigError>;

/// Error returned when an AIG operation failed.
#[derive(Debug, Error)]
pub enum AigError {
    /// A different node with the given id already exists.
    #[error("a different node with id={0} already exists")]
    DuplicateId(NodeId),

    /// The id 0 is reserved for the `False` constant node only.
    #[error("id=0 is for node False only")]
    IdZeroButNotFalse,

    /// The node with given id does not exist.
    #[error("node with id={0} does not exist")]
    NodeDoesNotExist(NodeId),

    /// Invalid operation on a node which does not have such specified fanin.
    /// Latches only have [`FaninId::Fanin0`].
    #[error("the node has no such fanin")]
    NoFanin,

    /// The AIG has reached an invalid state. This should never happen.
    /// For example, when tracking the nodes internally with the hashmap nodes,
    /// node `nodes[id]` should have id `id`. If this error is raised, my code is garbage.
    #[error("the AIG has reached an invalid state - this should not happen - error: {0}")]
    InvalidState(String),

    /// Just forwarding a [`MiterError`].
    ///
    /// [`MiterError`]: miter::MiterError
    #[error("{0}")]
    MiterError(#[from] MiterError),

    /// Just forwarding a [`ParserError`].
    #[error("{0}")]
    ParserError(#[from] ParserError),
}

/// Error returned when parsing from file failed.
///
/// It is defined here because the `parser` module is private.
#[derive(Debug, Error)]
pub enum ParserError {
    /// All features are not supported (only the basics in fact).
    #[error("unsupported feature: {0}")]
    UnsupportedFeature(String),

    /// Invalid token, something else was expected.
    #[error("invalid token: {0}")]
    InvalidToken(String),

    /// An IO error occured (file doesn't exist, or doesn't have the right extension, ...).
    #[error("io error: {0}")]
    IoError(String),
}
