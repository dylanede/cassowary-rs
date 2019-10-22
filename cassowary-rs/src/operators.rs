use std::ops;

use {
    Term,
    Expression,
    WeightedRelation,
    PartialConstraint,
    Constraint
};

/// A trait for creating constraints using your custom variable types without
/// using the BitOr hack.
pub trait Constrainable<Var>
where
    Var: Sized,
    Self: Sized
{
    fn equal_to<X>(self, x: X) -> Constraint<Var> where X: Into<Expression<Var>> + Clone;

    fn is<X>(self, x: X) -> Constraint<Var> where X: Into<Expression<Var>> + Clone {
        self.equal_to(x)
    }

    fn greater_than_or_equal_to<X>(self, x: X) -> Constraint<Var> where X: Into<Expression<Var>> + Clone;

    fn is_ge<X>(self, x: X) -> Constraint<Var> where X: Into<Expression<Var>> + Clone {
        self.greater_than_or_equal_to(x)
    }

    fn less_than_or_equal_to<X>(self, x: X) -> Constraint<Var> where X: Into<Expression<Var>> + Clone;

    fn is_le<X>(self, x: X) -> Constraint<Var> where X: Into<Expression<Var>> + Clone {
        self.less_than_or_equal_to(x)
    }
}


// WeightedRelation

impl<T: Clone> ops::BitOr<WeightedRelation> for Term<T> {
    type Output = PartialConstraint<T>;
    fn bitor(self, r: WeightedRelation) -> PartialConstraint<T> {
        PartialConstraint(self.into(), r)
    }
}
impl<T> ops::BitOr<WeightedRelation> for Expression<T> {
    type Output = PartialConstraint<T>;
    fn bitor(self, r: WeightedRelation) -> PartialConstraint<T> {
        PartialConstraint(self.into(), r)
    }
}

impl<T> ops::BitOr<f64> for PartialConstraint<T> {
    type Output = Constraint<T>;
    fn bitor(self, rhs: f64) -> Constraint<T> {
        let (op, s) = self.1.into();
        Constraint::new(self.0 - rhs, op, s)
    }
}
impl<T> ops::BitOr<f32> for PartialConstraint<T> {
    type Output = Constraint<T>;
    fn bitor(self, rhs: f32) -> Constraint<T> {
        self.bitor(rhs as f64)
    }
}

impl<T> ops::BitOr<Term<T>> for PartialConstraint<T> {
    type Output = Constraint<T>;
    fn bitor(self, rhs: Term<T>) -> Constraint<T> {
        let (op, s) = self.1.into();
        Constraint::new(self.0 - rhs, op, s)
    }
}
impl<T:Clone> ops::BitOr<Expression<T>> for PartialConstraint<T> {
    type Output = Constraint<T>;
    fn bitor(self, rhs: Expression<T>) -> Constraint<T> {
        let (op, s) = self.1.into();
        Constraint::new(self.0 - rhs, op, s)
    }
}

// Term

impl<T> ops::Mul<f64> for Term<T> {
    type Output = Term<T>;
    fn mul(mut self, v: f64) -> Term<T> {
        self *= v;
        self
    }
}

impl<T> ops::MulAssign<f64> for Term<T> {
    fn mul_assign(&mut self, v: f64) {
        *(self.coefficient.as_mut()) *= v;
    }
}

impl<T> ops::Mul<f32> for Term<T> {
    type Output = Term<T>;
    fn mul(self, v: f32) -> Term<T> {
        self.mul(v as f64)
    }
}

impl<T> ops::MulAssign<f32> for Term<T> {
    fn mul_assign(&mut self, v: f32) {
        self.mul_assign(v as f64)
    }
}

impl<T> ops::Mul<Term<T>> for f64 {
    type Output = Term<T>;
    fn mul(self, mut t: Term<T>) -> Term<T> {
        *(t.coefficient.as_mut()) *= self;
        t
    }
}

impl<T> ops::Mul<Term<T>> for f32 {
    type Output = Term<T>;
    fn mul(self, t: Term<T>) -> Term<T> {
        (self as f64).mul(t)
    }
}

impl<T> ops::Div<f64> for Term<T> {
    type Output = Term<T>;
    fn div(mut self, v: f64) -> Term<T> {
        self /= v;
        self
    }
}

impl<T> ops::DivAssign<f64> for Term<T> {
    fn div_assign(&mut self, v: f64) {
        *(self.coefficient.as_mut()) /= v;
    }
}

impl<T> ops::Div<f32> for Term<T> {
    type Output = Term<T>;
    fn div(self, v: f32) -> Term<T> {
        self.div(v as f64)
    }
}

impl<T> ops::DivAssign<f32> for Term<T> {
    fn div_assign(&mut self, v: f32) {
        self.div_assign(v as f64)
    }
}

impl<T:Clone> ops::Add<f64> for Term<T> {
    type Output = Expression<T>;
    fn add(self, v: f64) -> Expression<T> {
        Expression::new(vec![self], v)
    }
}

impl<T:Clone> ops::Add<f32> for Term<T> {
    type Output = Expression<T>;
    fn add(self, v: f32) -> Expression<T> {
        self.add(v as f64)
    }
}

impl<T:Clone> ops::Add<Term<T>> for f64 {
    type Output = Expression<T>;
    fn add(self, t: Term<T>) -> Expression<T> {
        Expression::new(vec![t], self)
    }
}

impl<T:Clone> ops::Add<Term<T>> for f32 {
    type Output = Expression<T>;
    fn add(self, t: Term<T>) -> Expression<T> {
        (self as f64).add(t)
    }
}

impl<T:Clone> ops::Add<Term<T>> for Term<T> {
    type Output = Expression<T>;
    fn add(self, t: Term<T>) -> Expression<T> {
        Expression::new(vec![self, t], 0.0)
    }
}

impl<T> ops::Add<Expression<T>> for Term<T> {
    type Output = Expression<T>;
    fn add(self, mut e: Expression<T>) -> Expression<T> {
        e.terms.push(self);
        e
    }
}

impl<T> ops::Add<Term<T>> for Expression<T> {
    type Output = Expression<T>;
    fn add(mut self, t: Term<T>) -> Expression<T> {
        self += t;
        self
    }
}

impl<T> ops::AddAssign<Term<T>> for Expression<T> {
    fn add_assign(&mut self, t: Term<T>) {
        self.terms.push(t);
    }
}

impl<T> ops::Neg for Term<T> {
    type Output = Term<T>;
    fn neg(mut self) -> Term<T> {
        *(self.coefficient.as_mut()) = -(self.coefficient.into_inner());
        self
    }
}

impl<T:Clone> ops::Sub<f64> for Term<T> {
    type Output = Expression<T>;
    fn sub(self, v: f64) -> Expression<T> {
        Expression::new(vec![self], -v)
    }
}

impl<T:Clone> ops::Sub<f32> for Term<T> {
    type Output = Expression<T>;
    fn sub(self, v: f32) -> Expression<T> {
        self.sub(v as f64)
    }
}

impl<T:Clone> ops::Sub<Term<T>> for f64 {
    type Output = Expression<T>;
    fn sub(self, t: Term<T>) -> Expression<T> {
        Expression::new(vec![-t], self)
    }
}

impl<T:Clone> ops::Sub<Term<T>> for f32 {
    type Output = Expression<T>;
    fn sub(self, t: Term<T>) -> Expression<T> {
        (self as f64).sub(t)
    }
}

impl<T:Clone> ops::Sub<Term<T>> for Term<T> {
    type Output = Expression<T>;
    fn sub(self, t: Term<T>) -> Expression<T> {
        Expression::new(vec![self, -t], 0.0)
    }
}

impl<T:Clone> ops::Sub<Expression<T>> for Term<T> {
    type Output = Expression<T>;
    fn sub(self, mut e: Expression<T>) -> Expression<T> {
        e.negate();
        e.terms.push(self);
        e
    }
}

impl<T> ops::Sub<Term<T>> for Expression<T> {
    type Output = Expression<T>;
    fn sub(mut self, t: Term<T>) -> Expression<T> {
        self -= t;
        self
    }
}

impl<T> ops::SubAssign<Term<T>> for Expression<T> {
    fn sub_assign(&mut self, t: Term<T>) {
        self.terms.push(-t);
    }
}

// Expression

impl<T:Clone> ops::Mul<f64> for Expression<T> {
    type Output = Expression<T>;
    fn mul(mut self, v: f64) -> Expression<T> {
        self *= v.clone();
        self
    }
}

impl<T:Clone> ops::MulAssign<f64> for Expression<T> {
    fn mul_assign(&mut self, v: f64) {
        *(self.constant.as_mut()) *= v;
        for t in &mut self.terms {
            *t = t.clone() * v;
        }
    }
}

impl<T:Clone> ops::Mul<f32> for Expression<T> {
    type Output = Expression<T>;
    fn mul(self, v: f32) -> Expression<T> {
        self.mul(v as f64)
    }
}

impl<T:Clone> ops::MulAssign<f32> for Expression<T> {
    fn mul_assign(&mut self, v: f32) {
        let v2 = v as f64;
        *(self.constant.as_mut()) *= v2;
        for t in &mut self.terms {
            *t = t.clone() * v2;
        }
    }
}

impl<T:Clone> ops::Mul<Expression<T>> for f64 {
    type Output = Expression<T>;
    fn mul(self, mut e: Expression<T>) -> Expression<T> {
        *(e.constant.as_mut()) *= self;
        for t in &mut e.terms {
            *t = t.clone() * self;
        }
        e
    }
}

impl<T:Clone> ops::Mul<Expression<T>> for f32 {
    type Output = Expression<T>;
    fn mul(self, e: Expression<T>) -> Expression<T> {
        (self as f64).mul(e)
    }
}

impl<T:Clone> ops::Div<f64> for Expression<T> {
    type Output = Expression<T>;
    fn div(mut self, v: f64) -> Expression<T> {
        self /= v;
        self
    }
}

impl<T:Clone> ops::DivAssign<f64> for Expression<T> {
    fn div_assign(&mut self, v: f64) {
        *(self.constant.as_mut()) /= v;
        for t in &mut self.terms {
            *t = t.clone() / v;
        }
    }
}

impl<T:Clone> ops::Div<f32> for Expression<T> {
    type Output = Expression<T>;
    fn div(self, v: f32) -> Expression<T> {
        self.div(v as f64)
    }
}

impl<T:Clone> ops::DivAssign<f32> for Expression<T> {
    fn div_assign(&mut self, v: f32) {
        self.div_assign(v as f64)
    }
}

impl<T> ops::Add<f64> for Expression<T> {
    type Output = Expression<T>;
    fn add(mut self, v: f64) -> Expression<T> {
        self += v;
        self
    }
}

impl<T> ops::AddAssign<f64> for Expression<T> {
    fn add_assign(&mut self, v: f64) {
        *(self.constant.as_mut()) += v;
    }
}

impl<T> ops::Add<f32> for Expression<T> {
    type Output = Expression<T>;
    fn add(self, v: f32) -> Expression<T> {
        self.add(v as f64)
    }
}

impl<T> ops::AddAssign<f32> for Expression<T> {
    fn add_assign(&mut self, v: f32) {
        self.add_assign(v as f64)
    }
}

impl<T> ops::Add<Expression<T>> for f64 {
    type Output = Expression<T>;
    fn add(self, mut e: Expression<T>) -> Expression<T> {
        *(e.constant.as_mut()) += self;
        e
    }
}

impl<T> ops::Add<Expression<T>> for f32 {
    type Output = Expression<T>;
    fn add(self, e: Expression<T>) -> Expression<T> {
        (self as f64).add(e)
    }
}

impl<T> ops::Add<Expression<T>> for Expression<T> {
    type Output = Expression<T>;
    fn add(mut self, e: Expression<T>) -> Expression<T> {
        self += e;
        self
    }
}

impl<T> ops::AddAssign<Expression<T>> for Expression<T> {
    fn add_assign(&mut self, mut e: Expression<T>) {
        self.terms.append(&mut e.terms);
        *(self.constant.as_mut()) += e.constant.into_inner();
    }
}

impl<T:Clone> ops::Neg for Expression<T> {
    type Output = Expression<T>;
    fn neg(mut self) -> Expression<T> {
        self.negate();
        self
    }
}

impl<T> ops::Sub<f64> for Expression<T> {
    type Output = Expression<T>;
    fn sub(mut self, v: f64) -> Expression<T> {
        self -= v;
        self
    }
}

impl<T> ops::SubAssign<f64> for Expression<T> {
    fn sub_assign(&mut self, v: f64) {
        *(self.constant.as_mut()) -= v;
    }
}

impl<T> ops::Sub<f32> for Expression<T> {
    type Output = Expression<T>;
    fn sub(self, v: f32) -> Expression<T> {
        self.sub(v as f64)
    }
}

impl<T> ops::SubAssign<f32> for Expression<T> {
    fn sub_assign(&mut self, v: f32) {
        self.sub_assign(v as f64)
    }
}

impl<T:Clone> ops::Sub<Expression<T>> for f64 {
    type Output = Expression<T>;
    fn sub(self, mut e: Expression<T>) -> Expression<T> {
        e.negate();
        *(e.constant.as_mut()) += self;
        e
    }
}

impl<T:Clone> ops::Sub<Expression<T>> for f32 {
    type Output = Expression<T>;
    fn sub(self, e: Expression<T>) -> Expression<T> {
        (self as f64).sub(e)
    }
}

impl<T:Clone> ops::Sub<Expression<T>> for Expression<T> {
    type Output = Expression<T>;
    fn sub(mut self, e: Expression<T>) -> Expression<T> {
        self -= e;
        self
    }
}

impl<T:Clone> ops::SubAssign<Expression<T>> for Expression<T> {
    fn sub_assign(&mut self, mut e: Expression<T>) {
        e.negate();
        self.terms.append(&mut e.terms);
        *(self.constant.as_mut()) += e.constant.into_inner();
    }
}
