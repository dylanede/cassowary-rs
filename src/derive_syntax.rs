#[macro_export]
macro_rules! derive_bitor_for {
  ( $x:ty ) => {
//    impl BitOr<WeightedRelation> for f64
//    {
//      type Output = PartialConstraint<$x>;
//      fn bitor(self, r: WeightedRelation) -> PartialConstraint<$x> {
//        PartialConstraint(self.into(), r)
//      }
//    }
//    impl BitOr<WeightedRelation> for f32 {
//      type Output = PartialConstraint<$x>;
//      fn bitor(self, r: WeightedRelation) -> PartialConstraint<$x> {
//        (self as f64).bitor(r)
//      }
//    }
    impl BitOr<WeightedRelation> for $x {
      type Output = PartialConstraint<$x>;
      fn bitor(self, r: WeightedRelation) -> PartialConstraint<$x> {
        PartialConstraint(self.into(), r)
      }
    }
  }
}

/// Derives operator support for your cassowary solver variable type.
/// This allows you to use your variable type in writing expressions, to a limited extent.
#[macro_export]
macro_rules! derive_syntax_for {
    ( $x:ty ) => {
        impl From<$x> for Expression<$x> {
            fn from(v: $x) -> Expression<$x> {
                Expression::from_term(Term::new(v, 1.0))
            }
        }

        impl Add<f64> for $x {
            type Output = Expression<$x>;
            fn add(self, v: f64) -> Expression<$x> {
                Expression::new(vec![Term::new(self, 1.0)], v)
            }
        }

        impl Add<f32> for $x {
            type Output = Expression<$x>;
            fn add(self, v: f32) -> Expression<$x> {
                self.add(v as f64)
            }
        }

        impl Add<$x> for f64 {
            type Output = Expression<$x>;
            fn add(self, v: $x) -> Expression<$x> {
                Expression::new(vec![Term::new(v, 1.0)], self)
            }
        }

        impl Add<$x> for f32 {
            type Output = Expression<$x>;
            fn add(self, v: $x) -> Expression<$x> {
                (self as f64).add(v)
            }
        }

        impl Add<$x> for $x {
            type Output = Expression<$x>;
            fn add(self, v: $x) -> Expression<$x> {
                Expression::new(vec![Term::new(self, 1.0), Term::new(v, 1.0)], 0.0)
            }
        }

        impl Add<Term<$x>> for $x {
            type Output = Expression<$x>;
            fn add(self, t: Term<$x>) -> Expression<$x> {
                Expression::new(vec![Term::new(self, 1.0), t], 0.0)
            }
        }

        impl Add<$x> for Term<$x> {
            type Output = Expression<$x>;
            fn add(self, v: $x) -> Expression<$x> {
                Expression::new(vec![self, Term::new(v, 1.0)], 0.0)
            }
        }

        impl Add<Expression<$x>> for $x {
            type Output = Expression<$x>;
            fn add(self, mut e: Expression<$x>) -> Expression<$x> {
                e.terms.push(Term::new(self, 1.0));
                e
            }
        }

        impl Add<$x> for Expression<$x> {
            type Output = Expression<$x>;
            fn add(mut self, v: $x) -> Expression<$x> {
                self += v;
                self
            }
        }

        impl AddAssign<$x> for Expression<$x> {
            fn add_assign(&mut self, v: $x) {
                self.terms.push(Term::new(v, 1.0));
            }
        }

        impl Neg for $x {
            type Output = Term<$x>;
            fn neg(self) -> Term<$x> {
                Term::new(self, -1.0)
            }
        }

        impl Sub<f64> for $x {
            type Output = Expression<$x>;
            fn sub(self, v: f64) -> Expression<$x> {
                Expression::new(vec![Term::new(self, 1.0)], -v)
            }
        }

        impl Sub<f32> for $x {
            type Output = Expression<$x>;
            fn sub(self, v: f32) -> Expression<$x> {
                self.sub(v as f64)
            }
        }

        impl Sub<$x> for f64 {
            type Output = Expression<$x>;
            fn sub(self, v: $x) -> Expression<$x> {
                Expression::new(vec![Term::new(v, -1.0)], self)
            }
        }

        impl Sub<$x> for f32 {
            type Output = Expression<$x>;
            fn sub(self, v: $x) -> Expression<$x> {
                (self as f64).sub(v)
            }
        }

        impl Sub<$x> for $x {
            type Output = Expression<$x>;
            fn sub(self, v: $x) -> Expression<$x> {
                Expression::new(vec![Term::new(self, 1.0), Term::new(v, -1.0)], 0.0)
            }
        }

        impl Sub<Term<$x>> for $x {
            type Output = Expression<$x>;
            fn sub(self, t: Term<$x>) -> Expression<$x> {
                Expression::new(vec![Term::new(self, 1.0), -t], 0.0)
            }
        }

        impl Sub<$x> for Term<$x> {
            type Output = Expression<$x>;
            fn sub(self, v: $x) -> Expression<$x> {
                Expression::new(vec![self, Term::new(v, -1.0)], 0.0)
            }
        }

        impl Sub<Expression<$x>> for $x {
            type Output = Expression<$x>;
            fn sub(self, mut e: Expression<$x>) -> Expression<$x> {
                e.negate();
                e.terms.push(Term::new(self, 1.0));
                e
            }
        }

        impl Sub<$x> for Expression<$x> {
            type Output = Expression<$x>;
            fn sub(mut self, v: $x) -> Expression<$x> {
                self -= v;
                self
            }
        }

        impl SubAssign<$x> for Expression<$x> {
            fn sub_assign(&mut self, v: $x) {
                self.terms.push(Term::new(v, -1.0));
            }
        }

        impl Mul<f64> for $x {
            type Output = Term<$x>;
            fn mul(self, v: f64) -> Term<$x> {
                Term::new(self, v)
            }
        }

        impl Mul<f32> for $x {
            type Output = Term<$x>;
            fn mul(self, v: f32) -> Term<$x> {
                self.mul(v as f64)
            }
        }

        impl Mul<$x> for f64 {
            type Output = Term<$x>;
            fn mul(self, v: $x) -> Term<$x> {
                Term::new(v, self)
            }
        }

        impl Mul<$x> for f32 {
            type Output = Term<$x>;
            fn mul(self, v: $x) -> Term<$x> {
                (self as f64).mul(v)
            }
        }

        impl Div<f64> for $x {
            type Output = Term<$x>;
            fn div(self, v: f64) -> Term<$x> {
                Term::new(self, 1.0 / v)
            }
        }

        impl Div<f32> for $x {
            type Output = Term<$x>;
            fn div(self, v: f32) -> Term<$x> {
                self.div(v as f64)
            }
        }

        impl BitOr<$x> for PartialConstraint<$x> {
            type Output = Constraint<$x>;
            fn bitor(self, rhs: $x) -> Constraint<$x> {
                let (op, s) = self.1.into();
                Constraint::new(self.0 - rhs, op, s)
            }
        }

        impl Constrainable<$x> for $x {
            fn equal_to<X>(self, x:X) -> Constraint<$x> where X: Into<Expression<$x>> + Clone {
                let lhs:Expression<$x> =
                    self
                    .into();
                let rhs:Expression<$x> =
                    x.into();
                lhs.equal_to(rhs)
            }
            fn greater_than_or_equal_to<X>(self, x:X) -> Constraint<$x> where X: Into<Expression<$x>> + Clone {
                let lhs:Expression<$x> =
                    self
                    .into();
                let rhs:Expression<$x> =
                    x.into();
                lhs.is_ge(rhs)
            }
            fn less_than_or_equal_to<X>(self, x:X) -> Constraint<$x> where X: Into<Expression<$x>> + Clone {
                let lhs:Expression<$x> =
                    self
                    .into();
                let rhs:Expression<$x> =
                    x.into();
                lhs.is_le(rhs)
            }
        }
    };
}


#[cfg(test)]
mod tests {
    use super::super::{
        Constrainable,
        Constraint,
        Expression,
        PartialConstraint,
        Solver,
        Term
    };

    use std::ops::*;


    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    enum VariableX {
        Left(usize), Width(usize)
    }
    derive_syntax_for!(VariableX);


    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    enum VariableY {
        Top(usize), Height(usize)
    }
    derive_syntax_for!(VariableY);


    struct Element(usize);


    impl Element {
        fn left(&self) -> VariableX {
            VariableX::Left(self.0)
        }
        fn width(&self) -> VariableX {
            VariableX::Width(self.0)
        }
        fn _top(&self) -> VariableX {
            VariableX::Left(self.0)
        }
        fn _height(&self) -> VariableX {
            VariableX::Width(self.0)
        }
    }


    #[test]
    fn can_do_ops() {
        let el0 =
            Element(0);
        let el1 =
            Element(1);

        let mut solver_x = Solver::new();
        solver_x
            .add_constraints(
                vec![
                    el0.left().is(0.0),
                    el0.width().is(100.0),
                    el1.left().is_ge(el0.left() + el0.width())
                ]
            )
            .unwrap();
        assert_eq!(solver_x.get_value(el0.left()), 0.0);
        assert_eq!(solver_x.get_value(el0.width()), 100.0);
        assert_eq!(solver_x.get_value(el1.left()), 100.0);
    }
}
