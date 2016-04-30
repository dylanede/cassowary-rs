//! This crate contains an implementation of the Cassowary constraint solving algorithm, based upon the work by
//! G.J. Badros et al. in 2001. This algorithm is designed primarily for use constraining elements in user interfaces.
//! Constraints are linear combinations of the problem variables. The notable features of Cassowary that make it
//! ideal for user interfaces are that it is incremental (i.e. you can add and remove constraints at runtime
//! and it will perform the minimum work to update the result) and that the constraints can be violated if
//! necessary,
//! with the order in which they are violated specified by setting a "strength" for each constraint.
//! This allows the solution to gracefully degrade, which is useful for when a
//! user interface needs to compromise on its constraints in order to still be able to display something.
//!
//! ## Constraint syntax
//!
//! This crate aims to provide syntax for describing linear constraints as naturally as possible, within
//! the limitations of Rust's type system. Generally you can write constraints as you would naturally, however
//! the operator symbol (for greater-than, less-than, equals) is replaced with an instance of the
//! `WeightedRelation` enum wrapped in "pipe brackets".
//!
//! For example, for the constraint
//! `(a + b) * 2 + c >= d + 1` with strength `s`, the code to use is
//!
//! ```ignore
//! (a + b) * 2.0 + c |GE(s)| d + 1.0
//! ```
//!
//! # A simple example
//!
//! Imagine a layout consisting of two elements laid out horizontally. For small window widths the elements
//! should compress to fit, but if there is enough space they should display at their preferred widths. The
//! first element will align to the left, and the second to the right. For  this example we will ignore
//! vertical layout.
//!
//! First we need to include the relevant parts of `cassowary`:
//!
//! ```
//! use cassowary::{ Solver, Variable };
//! use cassowary::WeightedRelation::*;
//! use cassowary::strength::{ WEAK, MEDIUM, STRONG, REQUIRED };
//! ```
//!
//! Let's define the variables required - the left and right edges of the elements, and the width of the window.
//!
//! ```ignore
//! let window_width = Variable::new();
//! struct Element {
//!    left: Variable,
//!    right: Variable
//! }
//! let box1 = Element {
//!     left: Variable::new(),
//!     right: Variable::new()
//! };
//! let box2 = Element {
//!     left: Variable::new(),
//!     right: Variable::new()
//! };
//! ```
//!
//! Now to set up the solver and constraints.
//!
//! ```ignore
//! let mut solver = Solver::new();
//! solver.add_constraints(&[window_width |GE(REQUIRED)| 0.0, // positive window width
//!                          box1.left |EQ(REQUIRED)| 0.0, // left align
//!                          box2.right |EQ(REQUIRED)| window_width, // right align
//!                          box2.left |GE(REQUIRED)| box1.right, // no overlap
//!                          // positive widths
//!                          box1.left |LE(REQUIRED)| box1.right,
//!                          box2.left |LE(REQUIRED)| box2.right,
//!                          // preferred widths:
//!                          box1.right - box1.left |EQ(WEAK)| 50.0,
//!                          box2.right - box2.left |EQ(WEAK)| 100.0]).unwrap();
//! ```
//!
//! The window width is currently free to take any positive value. Let's constrain it to a particular value.
//! Since for this example we will repeatedly change the window width, it is most efficient to use an
//! "edit variable", instead of repeatedly removing and adding constraints (note that for efficiency
//! reasons we cannot edit a normal constraint that has been added to the solver).
//!
//! ```ignore
//! solver.add_edit_variable(window_width, STRONG).unwrap();
//! solver.suggest_value(window_width, 300.0).unwrap();
//! ```
//!
//! This value of 300 is enough to fit both boxes in with room to spare, so let's check that this is the case.
//! To do this we need to tell the solver to update the values it has for the variables, then read them out.
//! In this example a closure is used to make reading out the values more concise.
//!
//! ```ignore
//! solver.update_variables();
//! {
//!     let value_of = |v| solver.value_for(v).unwrap();
//!     let (width, box1_left, box1_right, box2_left, box2_right) =
//!         (value_of(window_width),
//!          value_of(box1.left),
//!          value_of(box1.right),
//!          value_of(box2.left),
//!          value_of(box2.right));
//!
//!     println!("{}, {}, {}, {}, {}", width, box1_left, box1_right, box2_left, box2_right);
//! }
//! ```
//!
//! This should print `300, 0, 50, 200, 300`, as expected.
//!
//! Now let's try compressing the window so that the boxes can't take up their preferred widths.
//!
//! ```ignore
//! solver.suggest_value(window_width, 75.0);
//! solver.update_variables();
//!
//! {
//!     let value_of = |v| solver.value_for(v).unwrap();
//!     let (width, box1_left, box1_right, box2_left, box2_right) =
//!         (value_of(window_width),
//!          value_of(box1.left),
//!          value_of(box1.right),
//!          value_of(box2.left),
//!          value_of(box2.right));
//!
//!     println!("{}, {}, {}, {}, {}", width, box1_left, box1_right, box2_left, box2_right);
//! }
//! ```
//!
//! Now the solver can't satisfy all of the constraints. It will pick at least one of the weakest constraints to
//! violate. In this case it will be one or both of the preferred widths. For efficiency reasons this is picked
//! nondeterministically, so there are two possible results, `75, 0, 0, 0, 75` and `75, 0, 50, 50, 75`.
//! Due to the nature of the algorithm, "in-between" solutions, although just as valid, are not picked.
//!
//! In a user interface this is not likely a result we would prefer. The solution is to add another constraint
//! to control the behaviour when the preferred widths cannot both be satisfied. In this example we are going
//! to constrain the boxes to try to maintain a ratio between their widths.
//!
//! ```
//! # use cassowary::{ Solver, Variable };
//! # use cassowary::WeightedRelation::*;
//! # use cassowary::strength::{ WEAK, MEDIUM, STRONG, REQUIRED };
//! #
//! # let window_width = Variable::new();
//! # struct Element {
//! #    left: Variable,
//! #    right: Variable
//! # }
//! # let box1 = Element {
//! #     left: Variable::new(),
//! #     right: Variable::new()
//! # };
//! # let box2 = Element {
//! #     left: Variable::new(),
//! #     right: Variable::new()
//! # };
//! # let mut solver = Solver::new();
//! # solver.add_constraints(&[window_width |GE(REQUIRED)| 0.0, // positive window width
//! #                          box1.left |EQ(REQUIRED)| 0.0, // left align
//! #                          box2.right |EQ(REQUIRED)| window_width, // right align
//! #                          box2.left |GE(REQUIRED)| box1.right, // no overlap
//! #                          // positive widths
//! #                          box1.left |LE(REQUIRED)| box1.right,
//! #                          box2.left |LE(REQUIRED)| box2.right,
//! #                          // preferred widths:
//! #                          box1.right - box1.left |EQ(WEAK)| 50.0,
//! #                          box2.right - box2.left |EQ(WEAK)| 100.0]).unwrap();
//! # solver.add_edit_variable(window_width, STRONG).unwrap();
//! # solver.suggest_value(window_width, 300.0).unwrap();
//! # solver.update_variables();
//! # {
//! #     let value_of = |v| solver.value_for(v).unwrap();
//! #     let (width, box1_left, box1_right, box2_left, box2_right) =
//! #         (value_of(window_width),
//! #          value_of(box1.left),
//! #          value_of(box1.right),
//! #          value_of(box2.left),
//! #          value_of(box2.right));
//! #
//! #     println!("{}, {}, {}, {}, {}", width, box1_left, box1_right, box2_left, box2_right);
//! # }
//! # solver.suggest_value(window_width, 75.0);
//! # solver.update_variables();
//! #
//! # {
//! #     let value_of = |v| solver.value_for(v).unwrap();
//! #     let (width, box1_left, box1_right, box2_left, box2_right) =
//! #         (value_of(window_width),
//! #          value_of(box1.left),
//! #          value_of(box1.right),
//! #          value_of(box2.left),
//! #          value_of(box2.right));
//! #
//! #     println!("{}, {}, {}, {}, {}", width, box1_left, box1_right, box2_left, box2_right);
//! # }
//! solver.add_constraint(
//!     (box1.right - box1.left) / 50.0 |EQ(MEDIUM)| (box2.right - box2.left) / 100.0
//!     ).unwrap();
//!
//! solver.update_variables();
//! {
//!     let value_of = |v| solver.value_for(v).unwrap();
//!     let (width, box1_left, box1_right, box2_left, box2_right) =
//!         (value_of(window_width),
//!          value_of(box1.left),
//!          value_of(box1.right),
//!          value_of(box2.left),
//!          value_of(box2.right));
//!
//!     println!("{}, {}, {}, {}, {}", width, box1_left, box1_right, box2_left, box2_right);
//! }
//! ```
//!
//! Now the result is `75, 0, 25, 25, 75`, which as expected maintains the ratio between the two boxes.
//!
//! This example may have appeared somewhat contrived, but hopefully it shows the power of the cassowary
//! algorithm for laying out user interfaces.
//!
//! One thing that this example exposes is that this crate is a rather low level library. It does not have
//! any inherent knowledge of user interfaces, directions or boxes. Thus for use in a user interface this
//! crate should ideally be wrapped by a higher level API, which is outside the scope of this crate.
use std::sync::Arc;
use std::collections::HashMap;
use std::collections::hash_map::{Entry};

mod solver_impl;
mod operators;

static VARIABLE_ID: ::std::sync::atomic::AtomicUsize = ::std::sync::atomic::ATOMIC_USIZE_INIT;

/// Identifies a variable for the constraint solver.
/// Each new variable is unique in the view of the solver, but copying or cloning the variable produces
/// a copy of the same variable.
#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Variable(usize);

impl Variable {
    /// Produces a new unique variable for use in constraint solving.
    pub fn new() -> Variable {
        Variable(VARIABLE_ID.fetch_add(1, ::std::sync::atomic::Ordering::Relaxed))
    }
}

/// A variable and a coefficient to multiply that variable by. This is a sub-expression in
/// a constraint equation.
#[derive(Copy, Clone, Debug)]
pub struct Term {
    pub variable: Variable,
    pub coefficient: f64
}

impl Term {
    /// Construct a new Term from a variable and a coefficient.
    fn new(variable: Variable, coefficient: f64) -> Term {
        Term {
            variable: variable,
            coefficient: coefficient
        }
    }
}

/// An expression that can be the left hand or right hand side of a constraint equation.
/// It is a linear combination of variables, i.e. a sum of variables weighted by coefficients, plus an optional constant.
#[derive(Clone, Debug)]
pub struct Expression {
    pub terms: Vec<Term>,
    pub constant: f64
}

impl Expression {
    /// Constructs an expression of the form _n_, where n is a constant real number, not a variable.
    pub fn from_constant(v: f64) -> Expression {
        Expression {
            terms: Vec::new(),
            constant: v
        }
    }
    /// Constructs an expression from a single term. Forms an expression of the form _n x_
    /// where n is the coefficient, and x is the variable.
    pub fn from_term(term: Term) -> Expression {
        Expression {
            terms: vec![term],
            constant: 0.0
        }
    }
    /// General constructor. Each `Term` in `terms` is part of the sum forming the expression, as well as `constant`.
    pub fn new(terms: Vec<Term>, constant: f64) -> Expression {
        Expression {
            terms: terms,
            constant: constant
        }
    }
    /// Mutates this expression by multiplying it by minus one.
    pub fn negate(&mut self) {
        self.constant = -self.constant;
        for t in &mut self.terms {
            *t = -*t;
        }
    }
}

impl From<f64> for Expression {
    fn from(v: f64) -> Expression {
        Expression::from_constant(v)
    }
}

impl From<Variable> for Expression {
    fn from(v: Variable) -> Expression {
        Expression::from_term(Term::new(v, 1.0))
    }
}

impl From<Term> for Expression {
    fn from(t: Term) -> Expression {
        Expression::from_term(t)
    }
}

/// Contains useful constants and functions for producing strengths for use in the constraint solver.
/// Each constraint added to the solver has an associated strength specifying the precedence the solver should
/// impose when choosing which constraints to enforce. It will try to enforce all constraints, but if that
/// is impossible the lowest strength constraints are the first to be violated.
///
/// Strengths are simply real numbers. The strongest legal strength is 1,001,001,000.0. The weakest is 0.0.
/// For convenience constants are declared for commonly used strengths. These are `REQUIRED`, `STRONG`,
/// `MEDIUM` and `WEAK`. Feel free to multiply these by other values to get intermediate strengths.
/// Note that the solver will clip given strengths to the legal range.
///
/// `REQUIRED` signifies a constraint that cannot be violated under any circumstance. Use this special strength
/// sparingly, as the solver will fail completely if it find that not all of the `REQUIRED` constraints
/// can be satisfied. The other strengths represent fallible constraints. These should be the most
/// commonly used strenghts for use cases where violating a constraint is acceptable or even desired.
///
/// The solver will try to get as close to satisfying the constraints it violates as possible, strongest first.
/// This behaviour can be used (for example) to provide a "default" value for a variable should no other
/// stronger constraints be put upon it.
pub mod strength {
    /// Create a constraint as a linear combination of STRONG, MEDIUM and WEAK strengths, corresponding to `a`
    /// `b` and `c` respectively. The result is further multiplied by `w`.
    pub fn create(a: f64, b: f64, c: f64, w: f64) -> f64 {
        (a * w).max(0.0).min(1000.0) * 1_000_000.0 +
            (b * w).max(0.0).min(1000.0) * 1000.0 +
            (c * w).max(0.0).min(1000.0)
    }
    pub const REQUIRED: f64 = 1_001_001_000.0;
    pub const STRONG: f64 = 1_000_000.0;
    pub const MEDIUM: f64 = 1_000.0;
    pub const WEAK: f64 = 1.0;

    /// Clips a strength value to the legal range
    pub fn clip(s: f64) -> f64 {
        s.min(REQUIRED).max(0.0)
    }
}

/// The possible relations that a constraint can specify.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum RelationalOperator {
    /// `<=`
    LessOrEqual,
    /// `==`
    Equal,
    /// `>=`
    GreaterOrEqual
}

#[derive(Debug)]
struct ConstraintData {
    expression: Expression,
    strength: f64,
    op: RelationalOperator
}

/// A constraint, consisting of an equation goverened by an expression and a relational operator,
/// and an associated strength.
#[derive(Clone, Debug)]
pub struct Constraint(Arc<ConstraintData>);

impl Constraint {
    /// Construct a new constraint from an expression, a relational operator and a strength.
    /// This corresponds to the equation `e op 0.0`, e.g. `x + y >= 0.0`. For equations with a non-zero
    /// right hand side, subtract it from the equation to give a zero right hand side.
    pub fn new(e: Expression, op: RelationalOperator, strength: f64) -> Constraint {
        Constraint(Arc::new(ConstraintData {
            expression: e,
            op: op,
            strength: strength
        }))
    }
    /// The expression of the left hand side of the constraint equation.
    pub fn expr(&self) -> &Expression {
        &self.0.expression
    }
    /// The relational operator governing the constraint.
    pub fn op(&self) -> RelationalOperator {
        self.0.op
    }
    /// The strength of the constraint that the solver will use.
    pub fn strength(&self) -> f64 {
        self.0.strength
    }
}

impl ::std::hash::Hash for Constraint {
    fn hash<H: ::std::hash::Hasher>(&self, hasher: &mut H) {
        use ::std::ops::Deref;
        hasher.write_usize(self.0.deref() as *const _ as usize);
    }
}

impl PartialEq for Constraint {
    fn eq(&self, other: &Constraint) -> bool {
        use ::std::ops::Deref;
        self.0.deref() as *const _ == other.0.deref() as *const _
    }
}

impl Eq for Constraint {}

/// This is part of the syntactic sugar used for specifying constraints. This enum should be used as part of a
/// constraint expression. See the module documentation for more information.
pub enum WeightedRelation {
    /// `==`
    EQ(f64),
    /// `<=`
    LE(f64),
    /// `>=`
    GE(f64)
}
impl From<WeightedRelation> for (RelationalOperator, f64) {
    fn from(r: WeightedRelation) -> (RelationalOperator, f64) {
        use WeightedRelation::*;
        match r {
            EQ(s) => (RelationalOperator::Equal, s),
            LE(s) => (RelationalOperator::LessOrEqual, s),
            GE(s) => (RelationalOperator::GreaterOrEqual, s),
        }
    }
}

/// This is an intermediate type used in the syntactic sugar for specifying constraints. You should not use it
/// directly.
pub struct PartialConstraint(Expression, WeightedRelation);

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum SymbolType {
    Invalid,
    External,
    Slack,
    Error,
    Dummy
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Symbol(usize, SymbolType);

impl Symbol {
    fn invalid() -> Symbol { Symbol(0, SymbolType::Invalid) }
    fn type_(&self) -> SymbolType { self.1 }
}

#[derive(Clone)]
struct Row {
    cells: HashMap<Symbol, f64>,
    constant: f64
}

fn near_zero(value: f64) -> bool {
    const EPS: f64 = 1E-8;
    if value < 0.0 {
        -value < EPS
    } else {
        value < EPS
    }
}

impl Row {
    fn new(constant: f64) -> Row {
        Row {
            cells: HashMap::new(),
            constant: constant
        }
    }
    fn add(&mut self, v: f64) -> f64 {
        self.constant += v;
        self.constant
    }
    fn insert_symbol(&mut self, s: Symbol, coefficient: f64) {
        match self.cells.entry(s) {
            Entry::Vacant(entry) => if !near_zero(coefficient) {
                entry.insert(coefficient);
            },
            Entry::Occupied(mut entry) => {
                *entry.get_mut() += coefficient;
                if near_zero(*entry.get_mut()) {
                    entry.remove();
                }
            }
        }
    }

    fn insert_row(&mut self, other: &Row, coefficient: f64) {
        self.constant += other.constant * coefficient;
        for (s, v) in &other.cells {
            self.insert_symbol(*s, v * coefficient);
        }
    }

    fn remove(&mut self, s: Symbol) {
        self.cells.remove(&s);
    }

    fn reverse_sign(&mut self) {
        self.constant = -self.constant;
        for (_, v) in &mut self.cells {
            *v = -*v;
        }
    }

    fn solve_for_symbol(&mut self, s: Symbol) {
        let coeff = -1.0 / match self.cells.entry(s) {
            Entry::Occupied(entry) => entry.remove(),
            Entry::Vacant(_) => unreachable!()
        };
        self.constant *= coeff;
        for (_, v) in &mut self.cells {
            *v *= coeff;
        }
    }

    fn solve_for_symbols(&mut self, lhs: Symbol, rhs: Symbol) {
        self.insert_symbol(lhs, -1.0);
        self.solve_for_symbol(rhs);
    }

    fn coefficient_for(&self, s: Symbol) -> f64 {
        self.cells.get(&s).cloned().unwrap_or(0.0)
    }

    fn substitute(&mut self, s: Symbol, row: &Row) {
        if let Some(coeff) = self.cells.remove(&s) {
            self.insert_row(row, coeff)
        }
    }
}

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

/// The possible error conditions that `Solver::remove_constraint` can fail with.
#[derive(Debug, Copy, Clone)]
pub enum RemoveConstraintError {
    /// The constraint specified was not already in the solver, so cannot be removed.
    UnknownConstraint,
    /// The solver entered an invalid state. If this occurs please report the issue. This variant specifies
    /// additional details as a string.
    InternalSolverError(&'static str)
}

/// The possible error conditions that `Solver::add_edit_variable` can fail with.
#[derive(Debug, Copy, Clone)]
pub enum AddEditVariableError {
    /// The specified variable is already marked as an edit variable in the solver.
    DuplicateEditVariable,
    /// The specified strength was `REQUIRED`. This is illegal for edit variable strengths.
    BadRequiredStrength
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

/// The possible error conditions that `Solver::suggest_value` can fail with.
#[derive(Debug, Copy, Clone)]
pub enum SuggestValueError {
    /// The specified variable was not an edit variable in the solver, so cannot have its value suggested.
    UnknownEditVariable,
    /// The solver entered an invalid state. If this occurs please report the issue. This variant specifies
    /// additional details as a string.
    InternalSolverError(&'static str)
}

#[derive(Debug, Copy, Clone)]
struct InternalSolverError(&'static str);

pub use solver_impl::Solver;
