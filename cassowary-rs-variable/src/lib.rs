use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::ops::*;

use cassowary::{Constrainable, Constraint, Expression, PartialConstraint, Term, WeightedRelation};

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

cassowary::derive_syntax_for!(Variable);
cassowary::derive_bitor_for!(Variable);


#[cfg(test)]
mod tests {
    use cassowary::{Solver, Constraint};
    use super::Variable;
    use cassowary::WeightedRelation::*;
    use cassowary::strength::{ WEAK, MEDIUM, STRONG, REQUIRED };

    use std::cell::RefCell;
    use std::collections::HashMap;
    use std::rc::Rc;

    #[test]
    fn example() {
        let mut names = HashMap::new();
        fn print_changes(names: &HashMap<Variable, &'static str>, changes: &[(Variable, f64)]) {
            println!("Changes:");
            for &(ref var, ref val) in changes {
                println!("{}: {}", names[var], val);
            }
        }

        let window_width = Variable::new();
        names.insert(window_width, "window_width");
        struct Element {
            left: Variable,
            right: Variable
        }
        let box1 = Element {
            left: Variable::new(),
            right: Variable::new()
        };
        names.insert(box1.left, "box1.left");
        names.insert(box1.right, "box1.right");
        let box2 = Element {
            left: Variable::new(),
            right: Variable::new()
        };
        names.insert(box2.left, "box2.left");
        names.insert(box2.right, "box2.right");
        let mut solver = Solver::new();
        solver
            .add_constraints(
                vec![
                    window_width |GE(REQUIRED)| 0.0, // positive window width
                    box1.left |EQ(REQUIRED)| 0.0, // left align
                    box2.right |EQ(REQUIRED)| window_width, // right align
                    box2.left |GE(REQUIRED)| box1.right, // no overlap
                    // positive widths
                    box1.left |LE(REQUIRED)| box1.right,
                    box2.left |LE(REQUIRED)| box2.right,
                    // preferred widths:
                    box1.right - box1.left |EQ(WEAK)| 50.0,
                    box2.right - box2.left |EQ(WEAK)| 100.0
                ]
            )
            .unwrap();
        solver.add_edit_variable(window_width, STRONG).unwrap();
        solver.suggest_value(window_width, 300.0).unwrap();
        print_changes(&names, solver.fetch_changes());
        solver.suggest_value(window_width, 75.0).unwrap();
        print_changes(&names, solver.fetch_changes());
        solver.add_constraint(
            (box1.right - box1.left) / 50.0 |EQ(MEDIUM)| (box2.right - box2.left) / 100.0
        ).unwrap();
        print_changes(&names, solver.fetch_changes());
    }

    #[derive(Clone, Default)]
    struct Values(Rc<RefCell<HashMap<Variable, f64>>>);

    impl Values {
        fn value_of(&self, var: Variable) -> f64 {
            *self.0.borrow().get(&var).unwrap_or(&0.0)
        }
        fn update_values(&self, changes: &[(Variable, f64)]) {
            for &(ref var, ref value) in changes {
                println!("{:?} changed to {:?}", var, value);
                self.0.borrow_mut().insert(*var, *value);
            }
        }
    }

    pub fn new_values() -> (Box<Fn(Variable) -> f64>, Box<Fn(&[(Variable, f64)])>) {
        let values = Values(Rc::new(RefCell::new(HashMap::new())));
        let value_of = {
            let values = values.clone();
            move |v| values.value_of(v)
        };
        let update_values = {
            let values = values.clone();
            move |changes: &[_]| {
                values.update_values(changes);
            }
        };
        (Box::new(value_of), Box::new(update_values))
    }

    #[test]
    fn test_quadrilateral() {
        use cassowary::strength::{WEAK, STRONG, REQUIRED};
        struct Point {
            x: Variable,
            y: Variable
        }
        impl Point {
            fn new() -> Point {
                Point {
                    x: Variable::new(),
                    y: Variable::new()
                }
            }
        }
        let (value_of, update_values) = new_values();

        let points = [Point::new(),
                      Point::new(),
                      Point::new(),
                      Point::new()];
        let point_starts = [(10.0, 10.0), (10.0, 200.0), (200.0, 200.0), (200.0, 10.0)];
        let midpoints = [Point::new(),
                         Point::new(),
                         Point::new(),
                         Point::new()];
        let mut solver = Solver::new();
        let mut weight = 1.0;
        let multiplier = 2.0;
        for i in 0..4 {
            solver
                .add_constraints(
                    vec![points[i].x |EQ(WEAK * weight)| point_starts[i].0,
                         points[i].y |EQ(WEAK * weight)| point_starts[i].1]
                )
                .unwrap();
            weight *= multiplier;
        }

        for (start, end) in vec![(0, 1), (1, 2), (2, 3), (3, 0)] {
            solver
                .add_constraints(
                    vec![midpoints[start].x |EQ(REQUIRED)| (points[start].x + points[end].x) / 2.0,
                         midpoints[start].y |EQ(REQUIRED)| (points[start].y + points[end].y) / 2.0]
                )
                .unwrap();
        }

        solver
            .add_constraints(
                vec![points[0].x + 20.0 |LE(STRONG)| points[2].x,
                     points[0].x + 20.0 |LE(STRONG)| points[3].x,

                     points[1].x + 20.0 |LE(STRONG)| points[2].x,
                     points[1].x + 20.0 |LE(STRONG)| points[3].x,

                     points[0].y + 20.0 |LE(STRONG)| points[1].y,
                     points[0].y + 20.0 |LE(STRONG)| points[2].y,

                     points[3].y + 20.0 |LE(STRONG)| points[1].y,
                     points[3].y + 20.0 |LE(STRONG)| points[2].y]
            )
            .unwrap();

        for point in &points {
            solver
                .add_constraints(
                    vec![point.x |GE(REQUIRED)| 0.0,
                         point.y |GE(REQUIRED)| 0.0,

                         point.x |LE(REQUIRED)| 500.0,
                         point.y |LE(REQUIRED)| 500.0]
                )
                .unwrap()
        }

        update_values(solver.fetch_changes());

        assert_eq!([(value_of(midpoints[0].x), value_of(midpoints[0].y)),
                    (value_of(midpoints[1].x), value_of(midpoints[1].y)),
                    (value_of(midpoints[2].x), value_of(midpoints[2].y)),
                    (value_of(midpoints[3].x), value_of(midpoints[3].y))],
                   [(10.0, 105.0),
                    (105.0, 200.0),
                    (200.0, 105.0),
                    (105.0, 10.0)]);

        solver.add_edit_variable(points[2].x, STRONG).unwrap();
        solver.add_edit_variable(points[2].y, STRONG).unwrap();
        solver.suggest_value(points[2].x, 300.0).unwrap();
        solver.suggest_value(points[2].y, 400.0).unwrap();

        update_values(solver.fetch_changes());

        assert_eq!([(value_of(points[0].x), value_of(points[0].y)),
                    (value_of(points[1].x), value_of(points[1].y)),
                    (value_of(points[2].x), value_of(points[2].y)),
                    (value_of(points[3].x), value_of(points[3].y))],
                   [(10.0, 10.0),
                    (10.0, 200.0),
                    (300.0, 400.0),
                    (200.0, 10.0)]);

        assert_eq!([(value_of(midpoints[0].x), value_of(midpoints[0].y)),
                    (value_of(midpoints[1].x), value_of(midpoints[1].y)),
                    (value_of(midpoints[2].x), value_of(midpoints[2].y)),
                    (value_of(midpoints[3].x), value_of(midpoints[3].y))],
                   [(10.0, 105.0),
                    (155.0, 300.0),
                    (250.0, 205.0),
                    (105.0, 10.0)]);
    }

    #[test]
    fn remove_constraint() {
        let (value_of, update_values) = new_values();

        let mut solver = Solver::new();

        let val = Variable::new();

        let constraint: Constraint<Variable> = val | EQ(REQUIRED) | 100.0;
        solver.add_constraint(constraint.clone()).unwrap();
        update_values(solver.fetch_changes());

        assert_eq!(value_of(val), 100.0);

        solver.remove_constraint(&constraint).unwrap();
        solver.add_constraint(val | EQ(REQUIRED) | 0.0).unwrap();
        update_values(solver.fetch_changes());

        assert_eq!(value_of(val), 0.0);
    }
}
