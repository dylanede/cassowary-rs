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

impl From<Variable> for usize {
    fn from(v: Variable) -> usize {
        v.0
    }
}

impl From<Variable> for Expression<Variable> {
    fn from(v: Variable) -> Expression<Variable> {
        Expression::from_term(Term::new(v, 1.0))
    }
}


// Variable

impl Add<f64> for Variable {
    type Output = Expression<Variable>;
    fn add(self, v: f64) -> Expression<Variable> {
        Expression::new(vec![Term::new(self, 1.0)], v)
    }
}

impl Add<f32> for Variable {
    type Output = Expression<Variable>;
    fn add(self, v: f32) -> Expression<Variable> {
        self.add(v as f64)
    }
}

impl Add<Variable> for f64 {
    type Output = Expression<Variable>;
    fn add(self, v: Variable) -> Expression<Variable> {
        Expression::new(vec![Term::new(v, 1.0)], self)
    }
}

impl Add<Variable> for f32 {
    type Output = Expression<Variable>;
    fn add(self, v: Variable) -> Expression<Variable> {
        (self as f64).add(v)
    }
}

impl Add<Variable> for Variable {
    type Output = Expression<Variable>;
    fn add(self, v: Variable) -> Expression<Variable> {
        Expression::new(vec![Term::new(self, 1.0), Term::new(v, 1.0)], 0.0)
    }
}

impl Add<Term<Variable>> for Variable {
    type Output = Expression<Variable>;
    fn add(self, t: Term<Variable>) -> Expression<Variable> {
        Expression::new(vec![Term::new(self, 1.0), t], 0.0)
    }
}

impl Add<Variable> for Term<Variable> {
    type Output = Expression<Variable>;
    fn add(self, v: Variable) -> Expression<Variable> {
        Expression::new(vec![self, Term::new(v, 1.0)], 0.0)
    }
}

impl Add<Expression<Variable>> for Variable {
    type Output = Expression<Variable>;
    fn add(self, mut e: Expression<Variable>) -> Expression<Variable> {
        e.terms.push(Term::new(self, 1.0));
        e
    }
}

impl Add<Variable> for Expression<Variable> {
    type Output = Expression<Variable>;
    fn add(mut self, v: Variable) -> Expression<Variable> {
        self += v;
        self
    }
}

impl AddAssign<Variable> for Expression<Variable> {
    fn add_assign(&mut self, v: Variable) {
        self.terms.push(Term::new(v, 1.0));
    }
}

impl Neg for Variable {
    type Output = Term<Variable>;
    fn neg(self) -> Term<Variable> {
        Term::new(self, -1.0)
    }
}

impl Sub<f64> for Variable {
    type Output = Expression<Variable>;
    fn sub(self, v: f64) -> Expression<Variable> {
        Expression::new(vec![Term::new(self, 1.0)], -v)
    }
}

impl Sub<f32> for Variable {
    type Output = Expression<Variable>;
    fn sub(self, v: f32) -> Expression<Variable> {
        self.sub(v as f64)
    }
}

impl Sub<Variable> for f64 {
    type Output = Expression<Variable>;
    fn sub(self, v: Variable) -> Expression<Variable> {
        Expression::new(vec![Term::new(v, -1.0)], self)
    }
}

impl Sub<Variable> for f32 {
    type Output = Expression<Variable>;
    fn sub(self, v: Variable) -> Expression<Variable> {
        (self as f64).sub(v)
    }
}

impl Sub<Variable> for Variable {
    type Output = Expression<Variable>;
    fn sub(self, v: Variable) -> Expression<Variable> {
        Expression::new(vec![Term::new(self, 1.0), Term::new(v, -1.0)], 0.0)
    }
}

impl Sub<Term<Variable>> for Variable {
    type Output = Expression<Variable>;
    fn sub(self, t: Term<Variable>) -> Expression<Variable> {
        Expression::new(vec![Term::new(self, 1.0), -t], 0.0)
    }
}

impl Sub<Variable> for Term<Variable> {
    type Output = Expression<Variable>;
    fn sub(self, v: Variable) -> Expression<Variable> {
        Expression::new(vec![self, Term::new(v, -1.0)], 0.0)
    }
}

impl Sub<Expression<Variable>> for Variable {
    type Output = Expression<Variable>;
    fn sub(self, mut e: Expression<Variable>) -> Expression<Variable> {
        e.negate();
        e.terms.push(Term::new(self, 1.0));
        e
    }
}

impl Sub<Variable> for Expression<Variable> {
    type Output = Expression<Variable>;
    fn sub(mut self, v: Variable) -> Expression<Variable> {
        self -= v;
        self
    }
}

impl SubAssign<Variable> for Expression<Variable> {
    fn sub_assign(&mut self, v: Variable) {
        self.terms.push(Term::new(v, -1.0));
    }
}

impl Mul<f64> for Variable {
    type Output = Term<Variable>;
    fn mul(self, v: f64) -> Term<Variable> {
        Term::new(self, v)
    }
}

impl Mul<f32> for Variable {
    type Output = Term<Variable>;
    fn mul(self, v: f32) -> Term<Variable> {
        self.mul(v as f64)
    }
}

impl Mul<Variable> for f64 {
    type Output = Term<Variable>;
    fn mul(self, v: Variable) -> Term<Variable> {
        Term::new(v, self)
    }
}

impl Mul<Variable> for f32 {
    type Output = Term<Variable>;
    fn mul(self, v: Variable) -> Term<Variable> {
        (self as f64).mul(v)
    }
}

impl Div<f64> for Variable {
    type Output = Term<Variable>;
    fn div(self, v: f64) -> Term<Variable> {
        Term::new(self, 1.0 / v)
    }
}

impl Div<f32> for Variable {
    type Output = Term<Variable>;
    fn div(self, v: f32) -> Term<Variable> {
        self.div(v as f64)
    }
}

// Variable in relation to other syntax things
impl BitOr<Variable> for PartialConstraint<Variable> {
    type Output = Constraint<Variable>;
    fn bitor(self, rhs: Variable) -> Constraint<Variable> {
        let (op, s) = self.1.into();
        Constraint::new(self.0 - rhs, op, s)
    }
}
