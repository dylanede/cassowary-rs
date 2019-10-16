use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::ops::*;

use super::{Constraint, Expression, PartialConstraint, Term};

static VARIABLE_ID: AtomicUsize = AtomicUsize::new(0);

/// Identifies a variable for the constraint solver.
///
/// You can use this type as the `T` in Solver<T>). Alternatively, you can
/// implement your own variable type using this module as a guide.
///
/// Each new variable must be unique, identified by an internal key. Copying or
/// cloning the variable produces a copy of the same variable.
///
/// In order to use your custom variable type in the constraint syntax, use the
/// handy macro `derive_syntax_for`. See the source of this module for an
/// example.
#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Variable(usize);

impl Variable {
    /// Produces a new unique variable for use in constraint solving.
    pub fn new() -> Variable {
        Variable(VARIABLE_ID.fetch_add(1, Ordering::Relaxed))
    }

    /// An alternative to `new` which constructs a `Variable` with a
    /// user-defined key.
    ///
    /// Warning: when using this function, it is up to the user to ensure that
    /// each distinct variable gets a distinct key. It is advisable not to mix
    /// usage of this function with `Variable::new`, or at least to avoid
    /// specifying any keys near zero when using this function.
    pub fn from_usize(key: usize) -> Variable {
        Variable(key)
    }
}

derive_syntax_for!(Variable);
