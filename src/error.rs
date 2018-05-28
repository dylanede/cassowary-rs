use std::fmt;
use std::error::Error;

/// The possible error conditions that `Solver::add_constraint` can fail with.
#[derive(Debug, Copy, Clone)]
pub enum AddConstraintError {
    /// The constraint specified has already been added to the solver.
    DuplicateConstraint,
    /// The constraint is required, but it is unsatisfiable in conjunction with the existing constraints.
    UnsatisfiableConstraint,
    /// The solver entered an invalid state. If this occurs please report the issue. This variant specifies
    /// additional details as a string.
    InternalSolverError(&'static str)
}

impl fmt::Display for AddConstraintError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let AddConstraintError::InternalSolverError(msg) = self {
            write!(f, "internal solver error '{}'", msg)
        } else {
            write!(f, "{}", self.description())
        }
    }
}

impl Error for AddConstraintError {
    fn description(&self) -> &str {
        match self {
            AddConstraintError::DuplicateConstraint => 
                "constraint already added to the solver",
            AddConstraintError::UnsatisfiableConstraint => 
                "could not satisfy all required constraints",
            AddConstraintError::InternalSolverError(_) => 
                "internal solver error",
        }
    }
}

/// The possible error conditions that `Solver::remove_constraint` can fail with.
#[derive(Debug, Copy, Clone)]
pub enum RemoveConstraintError {
    /// The constraint specified was not already in the solver, so cannot be removed.
    UnknownConstraint,
    /// The solver entered an invalid state. If this occurs please report the issue. This variant specifies
    /// additional details as a string.
    InternalSolverError(&'static str)
}

impl fmt::Display for RemoveConstraintError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let RemoveConstraintError::InternalSolverError(msg) = self {
            write!(f, "internal solver error '{}'", msg)
        } else {
            write!(f, "{}", self.description())
        }
    }
}

impl Error for RemoveConstraintError {
    fn description(&self) -> &str {
        match self {
            RemoveConstraintError::UnknownConstraint => 
                "constraint is not in the solver",
            RemoveConstraintError::InternalSolverError(_) => 
                "internal solver error",
        }
    }
}

/// The possible error conditions that `Solver::add_edit_variable` can fail with.
#[derive(Debug, Copy, Clone)]
pub enum AddEditVariableError {
    /// The specified variable is already marked as an edit variable in the solver.
    DuplicateEditVariable,
    /// The specified strength was `REQUIRED`. This is illegal for edit variable strengths.
    BadRequiredStrength
}

impl fmt::Display for AddEditVariableError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.description())
    }
}

impl Error for AddEditVariableError {
    fn description(&self) -> &str {
        match self {
            AddEditVariableError::DuplicateEditVariable =>
                "variable already marked as an edit variable",
            AddEditVariableError::BadRequiredStrength => 
                "invalid strength for edit variable",
        }
    }
}

/// The possible error conditions that `Solver::remove_edit_variable` can fail with.
#[derive(Debug, Copy, Clone)]
pub enum RemoveEditVariableError {
    /// The specified variable was not an edit variable in the solver, so cannot be removed.
    UnknownEditVariable,
    /// The solver entered an invalid state. If this occurs please report the issue. This variant specifies
    /// additional details as a string.
    InternalSolverError(&'static str)
}

impl fmt::Display for RemoveEditVariableError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let RemoveEditVariableError::InternalSolverError(msg) = self {
            write!(f, "internal solver error '{}'", msg)
        } else {
            write!(f, "{}", self.description())
        }
    }
}

impl Error for RemoveEditVariableError {
    fn description(&self) -> &str {
        match self {
            RemoveEditVariableError::UnknownEditVariable =>
                "variable is not marked as an edit variable",
            RemoveEditVariableError::InternalSolverError(_) => 
                "internal solver error",
        }
    }
}

/// The possible error conditions that `Solver::suggest_value` can fail with.
#[derive(Debug, Copy, Clone)]
pub enum SuggestValueError {
    /// The specified variable was not an edit variable in the solver, so cannot have its value suggested.
    UnknownEditVariable,
    /// The solver entered an invalid state. If this occurs please report the issue. This variant specifies
    /// additional details as a string.
    InternalSolverError(&'static str)
}

impl fmt::Display for SuggestValueError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let SuggestValueError::InternalSolverError(msg) = self {
            write!(f, "internal solver error '{}'", msg)
        } else {
            write!(f, "{}", self.description())
        }
    }
}

impl Error for SuggestValueError {
    fn description(&self) -> &str {
        match self {
            SuggestValueError::UnknownEditVariable =>
                "variable is not marked as an edit variable",
            SuggestValueError::InternalSolverError(_) => 
                "internal solver error",
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub(crate) struct InternalSolverError(pub &'static str);
