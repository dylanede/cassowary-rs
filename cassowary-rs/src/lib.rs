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
//! ```ignore
//! extern crate cassowary_variable;
//! use cassowary::{ Solver };
//! use cassowary_variable::Variable;
//! use cassowary::WeightedRelation::*;
//! use cassowary::strength::{ WEAK, MEDIUM, STRONG, REQUIRED };
//! ```
//!
//! And we'll construct some conveniences for pretty printing (which should hopefully be self-explanatory):
//!
//! ```ignore
//! use std::collections::HashMap;
//! let mut names = HashMap::new();
//! fn print_changes(names: &HashMap<Variable, &'static str>, changes: &[(Variable, f64)]) {
//!     println!("Changes:");
//!     for &(ref var, ref val) in changes {
//!         println!("{}: {}", names[var], val);
//!     }
//! }
//! ```
//!
//! Let's define the variables required - the left and right edges of the elements, and the width of the window.
//!
//! ```ignore
//! let window_width = Variable::new();
//! names.insert(window_width, "window_width");
//!
//! struct Element {
//!     left: Variable,
//!     right: Variable
//! }
//! let box1 = Element {
//!     left: Variable::new(),
//!     right: Variable::new()
//! };
//! names.insert(box1.left, "box1.left");
//! names.insert(box1.right, "box1.right");
//!
//! let box2 = Element {
//!     left: Variable::new(),
//!     right: Variable::new()
//! };
//! names.insert(box2.left, "box2.left");
//! names.insert(box2.right, "box2.right");
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
//! We can fetch a list of changes to the values of variables in the solver. Using the pretty printer defined
//! earlier we can see what values our variables now hold.
//!
//! ```ignore
//! print_changes(&names, solver.fetch_changes());
//! ```
//!
//! This should print (in a possibly different order):
//!
//! ```ignore
//! Changes:
//! window_width: 300
//! box1.right: 50
//! box2.left: 200
//! box2.right: 300
//! ```
//!
//! Note that the value of `box1.left` is not mentioned. This is because `solver.fetch_changes` only lists
//! *changes* to variables, and since each variable starts in the solver with a value of zero, any values that
//! have not changed from zero will not be reported.
//!
//! Now let's try compressing the window so that the boxes can't take up their preferred widths.
//!
//! ```ignore
//! solver.suggest_value(window_width, 75.0);
//! print_changes(&names, solver.fetch_changes);
//! ```
//!
//! Now the solver can't satisfy all of the constraints. It will pick at least one of the weakest constraints to
//! violate. In this case it will be one or both of the preferred widths. For efficiency reasons this is picked
//! nondeterministically, so there are two possible results. This could be
//!
//! ```ignore
//! Changes:
//! window_width: 75
//! box1.right: 0
//! box2.left: 0
//! box2.right: 75
//! ```
//!
//! or
//!
//! ```ignore
//! Changes:
//! window_width: 75
//! box2.left: 50
//! box2.right: 75
//! ```
//!
//! Due to the nature of the algorithm, "in-between" solutions, although just as valid, are not picked.
//!
//! In a user interface this is not likely a result we would prefer. The solution is to add another constraint
//! to control the behaviour when the preferred widths cannot both be satisfied. In this example we are going
//! to constrain the boxes to try to maintain a ratio between their widths.
//!
//! These docs are all out of date:
//!
//! ```ignore
//! # use cassowary::Solver;
//! # use cassowary_variable::Variable;
//! # use cassowary::WeightedRelation::*;
//! # use cassowary::strength::{ WEAK, MEDIUM, STRONG, REQUIRED };
//! #
//! # use std::collections::HashMap;
//! # let mut names = HashMap::new();
//! # fn print_changes(names: &HashMap<Variable, &'static str>, changes: &[(Variable, f64)]) {
//! #     println!("Changes:");
//! #     for &(ref var, ref val) in changes {
//! #         println!("{}: {}", names[var], val);
//! #     }
//! # }
//! #
//! # let window_width = Variable::new();
//! # names.insert(window_width, "window_width");
//! # struct Element {
//! #    left: Variable,
//! #    right: Variable
//! # }
//! # let box1 = Element {
//! #     left: Variable::new(),
//! #     right: Variable::new()
//! # };
//! # names.insert(box1.left, "box1.left");
//! # names.insert(box1.right, "box1.right");
//! # let box2 = Element {
//! #     left: Variable::new(),
//! #     right: Variable::new()
//! # };
//! # names.insert(box2.left, "box2.left");
//! # names.insert(box2.right, "box2.right");
//! # let mut solver = Solver::new();
//! # solver
//! #     .add_constraints(
//! #         vec![window_width |GE(REQUIRED)| 0.0, // positive window width
//! #              box1.left |EQ(REQUIRED)| 0.0, // left align
//! #              box2.right |EQ(REQUIRED)| window_width, // right align
//! #              box2.left |GE(REQUIRED)| box1.right, // no overlap
//! #              // positive widths
//! #              box1.left |LE(REQUIRED)| box1.right,
//! #              box2.left |LE(REQUIRED)| box2.right,
//! #              // preferred widths:
//! #              box1.right - box1.left |EQ(WEAK)| 50.0,
//! #              box2.right - box2.left |EQ(WEAK)| 100.0]
//! #     )
//! #     .unwrap();
//! # solver.add_edit_variable(window_width, STRONG).unwrap();
//! # solver.suggest_value(window_width, 300.0).unwrap();
//! # print_changes(&names, solver.fetch_changes());
//! # solver.suggest_value(window_width, 75.0);
//! # print_changes(&names, solver.fetch_changes());
//! solver.add_constraint(
//!     (box1.right - box1.left) / 50.0 |EQ(MEDIUM)| (box2.right - box2.left) / 100.0
//!     ).unwrap();
//! print_changes(&names, solver.fetch_changes());
//! ```
//!
//! Now the result gives values that maintain the ratio between the sizes of the two boxes:
//!
//! ```ignore
//! Changes:
//! box1.right: 25
//! box2.left: 25
//! ```
//!
//! This example may have appeared somewhat contrived, but hopefully it shows the power of the cassowary
//! algorithm for laying out user interfaces.
//!
//! One thing that this example exposes is that this crate is a rather low level library. It does not have
//! any inherent knowledge of user interfaces, directions or boxes. Thus for use in a user interface this
//! crate should ideally be wrapped by a higher level API, which is outside the scope of this crate.
extern crate ordered_float;

use std::collections::HashMap;
use std::collections::hash_map::Entry;
use ordered_float::OrderedFloat;

mod solver_impl;
mod operators;
#[macro_use]
pub mod derive_syntax;


/// A variable and a coefficient to multiply that variable by. This is a sub-expression in
/// a constraint equation.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Term<T> {
    pub variable: T,
    pub coefficient: OrderedFloat<f64>
}

impl<T> Term<T> {
    /// Construct a new Term from a variable and a coefficient.
    pub fn new(variable: T, coefficient: f64) -> Term<T> {
        Term {
            variable: variable,
            coefficient: coefficient.into()
        }
    }
}

/// An expression that can be the left hand or right hand side of a constraint equation.
/// It is a linear combination of variables, i.e. a sum of variables weighted by coefficients, plus an optional constant.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Expression<T> {
    pub terms: Vec<Term<T>>,
    pub constant: OrderedFloat<f64>
}

impl<T: Clone> Expression<T> {
    /// Constructs an expression of the form _n_, where n is a constant real number, not a variable.
    pub fn from_constant(v: f64) -> Expression<T> {
        Expression {
            terms: Vec::new(),
            constant: v.into()
        }
    }
    /// Constructs an expression from a single term. Forms an expression of the form _n x_
    /// where n is the coefficient, and x is the variable.
    pub fn from_term(term: Term<T>) -> Expression<T> {
        Expression {
            terms: vec![term],
            constant: 0.0.into()
        }
    }
    /// General constructor. Each `Term` in `terms` is part of the sum forming the expression, as well as `constant`.
    pub fn new(terms: Vec<Term<T>>, constant: f64) -> Expression<T> {
        Expression {
            terms: terms,
            constant: constant.into()
        }
    }
    /// Mutates this expression by multiplying it by minus one.
    pub fn negate(&mut self) {
        self.constant = (-(self.constant.into_inner())).into();
        for t in &mut self.terms {
            let t2 = t.clone();
            *t = -t2;
        }
    }
}

impl<T: Clone> From<f64> for Expression<T> {
    fn from(v: f64) -> Expression<T> {
        Expression::from_constant(v)
    }
}

impl<T: Clone> From<Term<T>> for Expression<T> {
    fn from(t: Term<T>) -> Expression<T> {
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

impl std::fmt::Display for RelationalOperator {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        match *self {
            RelationalOperator::LessOrEqual => write!(fmt, "<=") ?,
            RelationalOperator::Equal => write!(fmt, "==") ?,
            RelationalOperator::GreaterOrEqual => write!(fmt, ">=") ?,
        };
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct ConstraintData<T> {
    expression: Expression<T>,
    strength: OrderedFloat<f64>,
    op: RelationalOperator
}

/// A constraint, consisting of an equation governed by an expression and a relational operator,
/// and an associated strength.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Constraint<T>(ConstraintData<T>);

impl<T> Constraint<T> {
    /// Construct a new constraint from an expression, a relational operator and a strength.
    /// This corresponds to the equation `e op 0.0`, e.g. `x + y >= 0.0`. For equations with a non-zero
    /// right hand side, subtract it from the equation to give a zero right hand side.
    pub fn new(e: Expression<T>, op: RelationalOperator, strength: f64) -> Constraint<T> {
        Constraint(ConstraintData {
            expression: e,
            op: op,
            strength: strength.into()
        })
    }
    /// The expression of the left hand side of the constraint equation.
    pub fn expr(&self) -> &Expression<T> {
        &self.0.expression
    }
    /// The relational operator governing the constraint.
    pub fn op(&self) -> RelationalOperator {
        self.0.op
    }
    /// The strength of the constraint that the solver will use.
    pub fn strength(&self) -> f64 {
        self.0.strength.into_inner()
    }
    /// Set the strength in builder-style
    pub fn with_strength(self, s:f64) -> Self {
        let mut c = self;
        c.0.strength = s.into();
        c
    }
}

/// This is part of the syntactic sugar used for specifying constraints. This enum should be used as part of a
/// constraint expression. See the module documentation for more information.
#[derive(Debug)]
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
#[derive(Debug)]
pub struct PartialConstraint<T>(pub Expression<T>, pub WeightedRelation);

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(Debug)]
enum SymbolType {
    Invalid,
    External,
    Slack,
    Error,
    Dummy
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(Debug)]
struct Symbol(usize, SymbolType);

impl Symbol {
    /// Choose the subject for solving for the row.
    ///
    /// This method will choose the best subject for using as the solve
    /// target for the row. An invalid symbol will be returned if there
    /// is no valid target.
    ///
    /// The symbols are chosen according to the following precedence:
    ///
    /// 1) The first symbol representing an external variable.
    /// 2) A negative slack or error tag variable.
    ///
    /// If a subject cannot be found, an invalid symbol will be returned.
    fn choose_subject(row: &Row, tag: &Tag) -> Symbol {
        for s in row.cells.keys() {
            if s.type_() == SymbolType::External {
                return *s
            }
        }
        if tag.marker.type_() == SymbolType::Slack || tag.marker.type_() == SymbolType::Error {
            if row.coefficient_for(tag.marker) < 0.0 {
                return tag.marker;
            }
        }
        if tag.other.type_() == SymbolType::Slack || tag.other.type_() == SymbolType::Error {
            if row.coefficient_for(tag.other) < 0.0 {
                return tag.other;
            }
        }
        Symbol::invalid()
    }

    fn invalid() -> Symbol { Symbol(0, SymbolType::Invalid) }
    fn type_(&self) -> SymbolType { self.1 }
}


#[derive(Copy, Clone)]
#[derive(Debug)]
struct Tag {
    marker: Symbol,
    other: Symbol
}


#[derive(Clone)]
#[derive(Debug)]
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
    pub fn new(constant: f64) -> Row {
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

    fn insert_row(&mut self, other: &Row, coefficient: f64) -> bool {
        let constant_diff = other.constant * coefficient;
        self.constant += constant_diff;
        for (s, v) in &other.cells {
            self.insert_symbol(*s, v * coefficient);
        }
        constant_diff != 0.0
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

    fn substitute(&mut self, s: Symbol, row: &Row) -> bool {
        if let Some(coeff) = self.cells.remove(&s) {
            self.insert_row(row, coeff)
        } else {
            false
        }
    }

    /// Test whether a row is composed of all dummy variables.
    fn all_dummies(&self) -> bool {
        for symbol in self.cells.keys() {
            if symbol.type_() != SymbolType::Dummy {
                return false;
            }
        }
        true
    }

    /// Get the first Slack or Error symbol in the row.
    ///
    /// If no such symbol is present, and Invalid symbol will be returned.
    /// Never returns an External symbol
    fn any_pivotable_symbol(&self) -> Symbol {
        for symbol in self.cells.keys() {
            if symbol.type_() == SymbolType::Slack || symbol.type_() == SymbolType::Error {
                return *symbol;
            }
        }
        Symbol::invalid()
    }

    /// Compute the entering variable for a pivot operation.
    ///
    /// This method will return first symbol in the objective function which
    /// is non-dummy and has a coefficient less than zero. If no symbol meets
    /// the criteria, it means the objective function is at a minimum, and an
    /// invalid symbol is returned.
    /// Could return an External symbol
    fn get_entering_symbol(&self) -> Symbol {
        for (symbol, value) in &self.cells {
            if symbol.type_() != SymbolType::Dummy && *value < 0.0 {
                return symbol.clone();
            }
        }
        Symbol::invalid()
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
