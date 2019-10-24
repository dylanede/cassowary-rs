use {
    Symbol,
    Tag,
    SymbolType,
    Constraint,
    Expression,
    Term,
    Row,
    AddConstraintError,
    RemoveConstraintError,
    InternalSolverError,
    SuggestValueError,
    AddEditVariableError,
    RemoveEditVariableError,
    RelationalOperator,
    near_zero
};

use std::collections::{ HashMap, HashSet };
use std::hash::Hash;
use std::fmt::Debug;
use std::collections::hash_map::Entry;


fn print_inc(msg: &str) {
    println!(">{}", msg);
}

fn print_dec(msg: &str) {
    println!("<{}", msg);
}


#[derive(Clone)]
#[derive(Debug)]
struct EditInfo<T> {
    tag: Tag,
    constraint: Constraint<T>,
    constant: f64
}

/// A constraint solver using the Cassowary algorithm. For proper usage please see the top level crate documentation.
#[derive(Debug)]
pub struct Solver<T>
where
    T: Debug + Clone + Eq + Hash
{
    cns: HashMap<Constraint<T>, Tag>,
    var_data: HashMap<T, (f64, Symbol, usize)>,
    var_for_symbol: HashMap<Symbol, T>,
    public_changes: Vec<(T, f64)>,
    changed: HashSet<T>,
    should_clear_changes: bool,
    rows: HashMap<Symbol, Row>,
    edits: HashMap<T, EditInfo<T>>,
    infeasible_rows: Vec<Symbol>, // never contains external symbols
    objective: Option<Row>,
    id_tick: usize
}

impl<T: Debug + Clone + Eq + Hash> Solver<T>
{
    /// Construct a new solver.
    pub fn new() -> Solver<T> {
        Solver {
            cns: HashMap::new(),
            var_data: HashMap::new(),
            var_for_symbol: HashMap::new(),
            public_changes: Vec::new(),
            changed: HashSet::new(),
            should_clear_changes: false,
            rows: HashMap::new(),
            edits: HashMap::new(),
            infeasible_rows: Vec::new(),
            objective: Some(Row::new(0.0)),
            id_tick: 1
        }
    }

    pub fn add_constraints<I: IntoIterator<Item = Constraint<T>>>(
        &mut self,
        constraints: I) -> Result<(), AddConstraintError>
    {
        for constraint in constraints {
            self.add_constraint(constraint)?;
        }
        Ok(())
    }

    /// Add a constraint to the solver.
    pub fn add_constraint(&mut self, constraint: Constraint<T>) -> Result<(), AddConstraintError> {
        if self.cns.contains_key(&constraint) {
            return Err(AddConstraintError::DuplicateConstraint);
        }

        // Creating a row causes symbols to reserved for the variables
        // in the constraint. If this method exits with an exception,
        // then its possible those variables will linger in the var map.
        // Since its likely that those variables will be used in other
        // constraints and since exceptional conditions are uncommon,
        // i'm not too worried about aggressive cleanup of the var map.
        let (mut row, tag) = self.create_row(&constraint);
        let mut subject = Symbol::choose_subject(&row, &tag);

        // If chooseSubject could find a valid entering symbol, one
        // last option is available if the entire row is composed of
        // dummy variables. If the constant of the row is zero, then
        // this represents redundant constraints and the new dummy
        // marker can enter the basis. If the constant is non-zero,
        // then it represents an unsatisfiable constraint.
        if subject.type_() == SymbolType::Invalid && row.all_dummies() {
            if !near_zero(*row.constant.as_ref()) {
                return Err(AddConstraintError::UnsatisfiableConstraint);
            } else {
                subject = tag.marker;
            }
        }

        // If an entering symbol still isn't found, then the row must
        // be added using an artificial variable. If that fails, then
        // the row represents an unsatisfiable constraint.
        if subject.type_() == SymbolType::Invalid {
            if !try!(self.add_with_artificial_variable(&row)
                     .map_err(|e| AddConstraintError::InternalSolverError(e.0))) {
                return Err(AddConstraintError::UnsatisfiableConstraint);
            }
        } else {
            row.solve_for_symbol(subject);
            self.substitute(subject, &row);
            if subject.type_() == SymbolType::External && *row.constant.as_ref() != 0.0 {
                let v:T = self.var_for_symbol[&subject].clone();
                self.var_changed(v);
            }
            self.rows.insert(subject, row);
        }

        self.cns.insert(constraint, tag);

        // Optimizing after each constraint is added performs less
        // aggregate work due to a smaller average system size. It
        // also ensures the solver remains in a consistent state.
        let mut objective = self.objective.take().expect("Could not take objective in add_constraint");
        self.optimise(&mut objective).map_err(|e| AddConstraintError::InternalSolverError(e.0))?;
        self.objective = Some(objective);
        Ok(())
    }

    /// Remove a constraint from the solver.
    pub fn remove_constraint(&mut self, constraint: &Constraint<T>) -> Result<(), RemoveConstraintError> {
        let tag = self.cns.remove(constraint).ok_or(RemoveConstraintError::UnknownConstraint)?;

        // Remove the error effects from the objective function
        // *before* pivoting, or substitutions into the objective
        // will lead to incorrect solver results.
        self.remove_constraint_effects(constraint, &tag);

        // If the marker is basic, simply drop the row. Otherwise,
        // pivot the marker into the basis and then drop the row.
        if let None = self.rows.remove(&tag.marker) {
            let (leaving, mut row) =
                self.get_marker_leaving_row(tag.marker)
                .ok_or(
                    RemoveConstraintError::InternalSolverError(
                        "Failed to find leaving row."
                    )
                )?;
            row.solve_for_symbols(leaving, tag.marker);
            self.substitute(tag.marker, &row);
        }

        // Optimizing after each constraint is removed ensures that the
        // solver remains consistent. It makes the solver api easier to
        // use at a small tradeoff for speed.
        let mut objective = self.objective.take().expect("Could not take objective in remove_constraint");
        self.optimise(&mut objective).map_err(|e| RemoveConstraintError::InternalSolverError(e.0))?;
        self.objective = Some(objective);

        // Check for and decrease the reference count for variables referenced by the constraint
        // If the reference count is zero remove the variable from the variable map
        for term in &constraint.expr().terms {
            if !near_zero(term.coefficient.into_inner()) {
                let mut should_remove = false;
                if let Some(&mut (_, _, ref mut count)) = self.var_data.get_mut(&term.variable) {
                    *count -= 1;
                    should_remove = *count == 0;
                }
                if should_remove {
                    self.var_for_symbol.remove(&self.var_data[&term.variable].1);
                    self.var_data.remove(&term.variable);
                }
            }
        }
        Ok(())
    }

    /// Test whether a constraint has been added to the solver.
    pub fn has_constraint(&self, constraint: &Constraint<T>) -> bool {
        self.cns.contains_key(constraint)
    }

    /// Add an edit variable to the solver.
    ///
    /// This method should be called before the `suggest_value` method is
    /// used to supply a suggested value for the given edit variable.
    pub fn add_edit_variable(&mut self, v: T, strength: f64) -> Result<(), AddEditVariableError> {
        if self.edits.contains_key(&v) {
            return Err(AddEditVariableError::DuplicateEditVariable);
        }
        let strength = ::strength::clip(strength);
        if strength == ::strength::REQUIRED {
            return Err(AddEditVariableError::BadRequiredStrength);
        }
        let cn = Constraint::new(Expression::from_term(Term::new(v.clone(), 1.0)),
                                 RelationalOperator::Equal,
                                 strength);
        self
            .add_constraint(cn.clone())
            .expect("Could not add constraint in add_edit_variable");
        self.edits.insert(v.clone(), EditInfo {
            tag: self.cns[&cn].clone(),
            constraint: cn,
            constant: 0.0
        });
        Ok(())
    }

    /// Remove an edit variable from the solver.
    pub fn remove_edit_variable(&mut self, v: T) -> Result<(), RemoveEditVariableError> {
        if let Some(constraint) = self.edits.remove(&v).map(|e| e.constraint) {
            try!(self.remove_constraint(&constraint)
                 .map_err(|e| match e {
                     RemoveConstraintError::UnknownConstraint =>
                         RemoveEditVariableError::InternalSolverError("Edit constraint not in system"),
                     RemoveConstraintError::InternalSolverError(s) =>
                         RemoveEditVariableError::InternalSolverError(s)
                 }));
            Ok(())
        } else {
            Err(RemoveEditVariableError::UnknownEditVariable)
        }
    }

    /// Test whether an edit variable has been added to the solver.
    pub fn has_edit_variable(&self, v: &T) -> bool {
        self.edits.contains_key(v)
    }

    /// Suggest a value for the given edit variable.
    ///
    /// This method should be used after an edit variable has been added to
    /// the solver in order to suggest the value for that variable.
    pub fn suggest_value(&mut self, variable: T, value: f64) -> Result<(), SuggestValueError> {
        let (info_tag_marker, info_tag_other, delta) = {
            let info = self.edits.get_mut(&variable).ok_or(SuggestValueError::UnknownEditVariable)?;
            let delta = value - info.constant;
            info.constant = value;
            (info.tag.marker, info.tag.other, delta)
        };
        // tag.marker and tag.other are never external symbols

        // The nice version of the following code runs into non-lexical borrow issues.
        // Ideally the `if row...` code would be in the body of the if. Pretend that it is.
        {
            let infeasible_rows = &mut self.infeasible_rows;
            if self.rows.get_mut(&info_tag_marker)
                .map(|row|
                     if row.add(-delta) < 0.0 {
                         infeasible_rows.push(info_tag_marker);
                     }).is_some()
            {

            } else if self.rows.get_mut(&info_tag_other)
                .map(|row|
                     if row.add(delta) < 0.0 {
                         infeasible_rows.push(info_tag_other);
                     }).is_some()
            {

            } else {
                for (symbol, row) in &mut self.rows {
                    let coeff = row.coefficient_for(info_tag_marker);
                    let diff = delta * coeff;
                    if diff != 0.0 && symbol.type_() == SymbolType::External {
                        let v = self.var_for_symbol[symbol].clone();
                        // inline var_changed - borrow checker workaround
                        if self.should_clear_changes {
                            self.changed.clear();
                            self.should_clear_changes = false;
                        }
                        self.changed.insert(v);
                    }
                    if coeff != 0.0 &&
                        row.add(diff) < 0.0 &&
                        symbol.type_() != SymbolType::External
                    {
                        infeasible_rows.push(*symbol);
                    }
                }
            }
        }
        self.dual_optimise().map_err(|e| SuggestValueError::InternalSolverError(e.0))?;
        return Ok(());
    }

    fn var_changed(&mut self, v: T) {
        if self.should_clear_changes {
            self.changed.clear();
            self.should_clear_changes = false;
        }
        self.changed.insert(v);
    }

    /// Fetches all changes to the values of variables since the last call to this function.
    ///
    /// The list of changes returned is not in a specific order. Each change comprises the variable changed and
    /// the new value of that variable.
    pub fn fetch_changes(&mut self) -> &[(T, f64)] {
        if self.should_clear_changes {
            self.changed.clear();
            self.should_clear_changes = false;
        } else {
            self.should_clear_changes = true;
        }
        self.public_changes.clear();
        for v in &self.changed {
            if let Some(var_data) = self.var_data.get_mut(&v) {
                let new_value = self.rows.get(&var_data.1).map(|r| r.constant).map(|o| o.into_inner()).unwrap_or(0.0);
                let old_value = var_data.0;
                if old_value != new_value {
                    self.public_changes.push((v.clone(), new_value));
                    var_data.0 = new_value;
                }
            }
        }
        &self.public_changes
    }

    /// Reset the solver to the empty starting condition.
    ///
    /// This method resets the internal solver state to the empty starting
    /// condition, as if no constraints or edit variables have been added.
    /// This can be faster than deleting the solver and creating a new one
    /// when the entire system must change, since it can avoid unnecessary
    /// heap (de)allocations.
    pub fn reset(&mut self) {
        self.rows.clear();
        self.cns.clear();
        self.var_data.clear();
        self.var_for_symbol.clear();
        self.changed.clear();
        self.should_clear_changes = false;
        self.edits.clear();
        self.infeasible_rows.clear();
        self.objective = Some(Row::new(0.0));
        self.id_tick = 1;
    }

    /// Get the symbol for the given variable.
    ///
    /// If a symbol does not exist for the variable, one will be created.
    fn get_var_symbol(&mut self, v: T) -> Symbol {
        let id_tick = &mut self.id_tick;
        let var_for_symbol = &mut self.var_for_symbol;
        let value = self.var_data.entry(v.clone()).or_insert_with(|| {
            let s = Symbol(*id_tick, SymbolType::External);
            var_for_symbol.insert(s, v);
            *id_tick += 1;
            (std::f64::NAN, s, 0)
        });
        value.2 += 1;
        value.1
    }

    /// Create a new Row object for the given constraint.
    ///
    /// The terms in the constraint will be converted to cells in the row.
    /// Any term in the constraint with a coefficient of zero is ignored.
    /// This method uses the `getVarSymbol` method to get the symbol for
    /// the variables added to the row. If the symbol for a given cell
    /// variable is basic, the cell variable will be substituted with the
    /// basic row.
    ///
    /// The necessary slack and error variables will be added to the row.
    /// If the constant for the row is negative, the sign for the row
    /// will be inverted so the constant becomes positive.
    ///
    /// The tag will be updated with the marker and error symbols to use
    /// for tracking the movement of the constraint in the tableau.
    fn create_row(&mut self, constraint: &Constraint<T>) -> (Row, Tag) {
        let expr = constraint.expr();
        let mut row = Row::new(expr.constant.into_inner());
        // Substitute the current basic variables into the row.
        for term in &expr.terms {
            if !near_zero(term.coefficient.into_inner()) {
                let symbol = self.get_var_symbol(term.variable.clone());
                if let Some(other_row) = self.rows.get(&symbol) {
                    row.insert_row(other_row, term.coefficient.into_inner());
                } else {
                    row.insert_symbol(symbol, term.coefficient.into_inner());
                }
            }
        }

        let mut objective = self.objective.take().expect("Could not take objective in create_row");
        // Add the necessary slack, error, and dummy variables.
        let tag = match constraint.op() {
            RelationalOperator::GreaterOrEqual |
            RelationalOperator::LessOrEqual => {
                let coeff = if constraint.op() == RelationalOperator::LessOrEqual {
                    1.0
                } else {
                    -1.0
                };
                let slack = Symbol(self.id_tick, SymbolType::Slack);
                self.id_tick += 1;
                row.insert_symbol(slack, coeff);
                if constraint.strength() < ::strength::REQUIRED {
                    let error = Symbol(self.id_tick, SymbolType::Error);
                    self.id_tick += 1;
                    row.insert_symbol(error, -coeff);
                    objective.insert_symbol(error, constraint.strength());
                    Tag {
                        marker: slack,
                        other: error
                    }
                } else {
                    Tag {
                        marker: slack,
                        other: Symbol::invalid()
                    }
                }
            }
            RelationalOperator::Equal => {
                if constraint.strength() < ::strength::REQUIRED {
                    let errplus = Symbol(self.id_tick, SymbolType::Error);
                    self.id_tick += 1;
                    let errminus = Symbol(self.id_tick, SymbolType::Error);
                    self.id_tick += 1;
                    row.insert_symbol(errplus, -1.0); // v = eplus - eminus
                    row.insert_symbol(errminus, 1.0); // v - eplus + eminus = 0
                    objective.insert_symbol(errplus, constraint.strength());
                    objective.insert_symbol(errminus, constraint.strength());
                    Tag {
                        marker: errplus,
                        other: errminus
                    }
                } else {
                    let dummy = Symbol(self.id_tick, SymbolType::Dummy);
                    self.id_tick += 1;
                    row.insert_symbol(dummy, 1.0);
                    Tag {
                        marker: dummy,
                        other: Symbol::invalid()
                    }
                }
            }
        };
        self.objective = Some(objective);

        // Ensure the row has a positive constant.
        if *row.constant.as_ref() < 0.0 {
            row.reverse_sign();
        }

        print_dec("objective:ref mut out");
        (row, tag)
    }

    /// Add the row to the tableau using an artificial variable.
    ///
    /// This will return false if the constraint cannot be satisfied.
    fn add_with_artificial_variable(&mut self, row: &Row) -> Result<bool, InternalSolverError> {
        // Create and add the artificial variable to the tableau
        let art = Symbol(self.id_tick, SymbolType::Slack);
        self.id_tick += 1;
        self.rows.insert(art, row.clone());

        // Optimize the artificial objective. This is successful
        // only if the artificial objective is optimized to zero.
        let mut artificial:Row = row.clone();
        self.optimise(&mut artificial)?;
        let success = near_zero(*artificial.constant.as_ref());

        // If the artificial variable is basic, pivot the row so that
        // it becomes basic. If the row is constant, exit early.
        if let Some(mut row) = self.rows.remove(&art) {
            if row.cells.is_empty() {
                return Ok(success);
            }
            let entering = row.any_pivotable_symbol(); // never External
            if entering.type_() == SymbolType::Invalid {
                return Ok(false); // unsatisfiable (will this ever happen?)
            }
            row.solve_for_symbols(art, entering);
            self.substitute(entering, &row);
            self.rows.insert(entering, row);
        }

        // Remove the artificial row from the tableau
        for (_, row) in &mut self.rows {
            row.remove(art);
        }
        self.objective
            .as_mut()
            .expect("Could not mutate objective in add_with_artificial_variable")
            .remove(art);
        Ok(success)
    }

    /// Substitute the parametric symbol with the given row.
    ///
    /// This method will substitute all instances of the parametric symbol
    /// in the tableau and the objective function with the given row.
    fn substitute(&mut self, symbol: Symbol, row: &Row) {
        for (&other_symbol, other_row) in &mut self.rows {
            let constant_changed = other_row.substitute(symbol, row);
            if other_symbol.type_() == SymbolType::External && constant_changed {
                // inline var_changed
                if self.should_clear_changes {
                    self.changed.clear();
                    self.should_clear_changes = false;
                }
                let v = self.var_for_symbol[&other_symbol].clone();
                self.changed.insert(v);
            }
            if other_symbol.type_() != SymbolType::External && *other_row.constant.as_ref() < 0.0 {
                self.infeasible_rows.push(other_symbol);
            }
        }
    }

    /// Optimize the system for the given objective function.
    ///
    /// This method performs iterations of Phase 2 of the simplex method
    /// until the objective function reaches a minimum.
    ///
    /// Returns the optimized objective function.
    fn optimise(&mut self, objective: &mut Row) -> Result<(), InternalSolverError> {
        'optimisation: loop {
            let entering = objective.get_entering_symbol();
            if entering.type_() == SymbolType::Invalid {
                break 'optimisation;
            }
            let (leaving, mut row) =
                self
                .get_leaving_row(entering)
                .ok_or(InternalSolverError("The objective is unbounded"))?;
            // pivot the entering symbol into the basis
            row.solve_for_symbols(leaving, entering);
            self.substitute(entering, &row);
            objective.substitute(entering, &row);
            if entering.type_() == SymbolType::External && *row.constant.as_ref() != 0.0 {
                let v = self.var_for_symbol[&entering].clone();
                self.var_changed(v);
            }
            self.rows.insert(entering, row);
        }
        Ok(())
    }

    /// Optimize the system using the dual of the simplex method.
    ///
    /// The current state of the system should be such that the objective
    /// function is optimal, but not feasible. This method will perform
    /// an iteration of the dual simplex method to make the solution both
    /// optimal and feasible.
    fn dual_optimise(&mut self) -> Result<(), InternalSolverError> {
        while !self.infeasible_rows.is_empty() {
            let leaving = self.infeasible_rows.pop().unwrap();

            let row = if let Entry::Occupied(entry) = self.rows.entry(leaving) {
                if *entry.get().constant.as_ref() < 0.0 {
                    Some(entry.remove())
                } else {
                    None
                }
            } else {
                None
            };
            if let Some(mut row) = row {
                let entering = self.get_dual_entering_symbol(&row);
                if entering.type_() == SymbolType::Invalid {
                    return Err(InternalSolverError("Dual optimise failed."));
                }
                // pivot the entering symbol into the basis
                row.solve_for_symbols(leaving, entering);
                self.substitute(entering, &row);
                if entering.type_() == SymbolType::External && *row.constant.as_ref() != 0.0 {
                    let v = self.var_for_symbol[&entering].clone();
                    self.var_changed(v);
                }
                self.rows.insert(entering, row);
            }
        }
        Ok(())
    }

    /// Compute the entering symbol for the dual optimize operation.
    ///
    /// This method will return the symbol in the row which has a positive
    /// coefficient and yields the minimum ratio for its respective symbol
    /// in the objective function. The provided row *must* be infeasible.
    /// If no symbol is found which meats the criteria, an invalid symbol
    /// is returned.
    /// Could return an External symbol
    fn get_dual_entering_symbol(&self, row: &Row) -> Symbol {
        let mut entering = Symbol::invalid();
        let mut ratio = std::f64::INFINITY;
        let objective =
            self.objective.as_ref().expect("Could not get objective in get_dual_entering_symbol");
        for (symbol, value) in &row.cells {
            let value = *value.as_ref();
            if value > 0.0 && symbol.type_() != SymbolType::Dummy {
                let coeff = objective.coefficient_for(*symbol);
                let r = coeff / value;
                if r < ratio {
                    ratio = r;
                    entering = *symbol;
                }
            }
        }
        entering
    }

    /// Compute the row which holds the exit symbol for a pivot.
    ///
    /// This method will return an iterator to the row in the row map
    /// which holds the exit symbol. If no appropriate exit symbol is
    /// found, the end() iterator will be returned. This indicates that
    /// the objective function is unbounded.
    /// Never returns a row for an External symbol
    fn get_leaving_row(&mut self, entering: Symbol) -> Option<(Symbol, Row)> {
        let mut ratio = std::f64::INFINITY;
        let mut found = None;
        for (symbol, row) in &self.rows {
            if symbol.type_() != SymbolType::External {
                let temp = row.coefficient_for(entering);
                if temp < 0.0 {
                    let temp_ratio = -row.constant.as_ref() / temp;
                    if temp_ratio < ratio {
                        ratio = temp_ratio;
                        found = Some(*symbol);
                    }
                }
            }
        }
        found.map(|s| (s, self.rows.remove(&s).unwrap()))
    }

    /// Compute the leaving row for a marker variable.
    ///
    /// This method will return an iterator to the row in the row map
    /// which holds the given marker variable. The row will be chosen
    /// according to the following precedence:
    ///
    /// 1) The row with a restricted basic varible and a negative coefficient
    ///    for the marker with the smallest ratio of -constant / coefficient.
    ///
    /// 2) The row with a restricted basic variable and the smallest ratio
    ///    of constant / coefficient.
    ///
    /// 3) The last unrestricted row which contains the marker.
    ///
    /// If the marker does not exist in any row, the row map end() iterator
    /// will be returned. This indicates an internal solver error since
    /// the marker *should* exist somewhere in the tableau.
    fn get_marker_leaving_row(&mut self, marker: Symbol) -> Option<(Symbol, Row)> {
        let mut r1 = std::f64::INFINITY;
        let mut r2 = r1;
        let mut first = None;
        let mut second = None;
        let mut third = None;
        for (symbol, row) in &self.rows {
            let c = row.coefficient_for(marker);
            let row_constant = row.constant.as_ref();
            if c == 0.0 {
                continue;
            }
            if symbol.type_() == SymbolType::External {
                third = Some(*symbol);
            } else if c < 0.0 {
                let r = -row_constant / c;
                if r < r1 {
                    r1 = r;
                    first = Some(*symbol);
                }
            } else {
                let r = row_constant / c;
                if r < r2 {
                    r2 = r;
                    second = Some(*symbol);
                }
            }
        }
        first
            .or(second)
            .or(third)
            .and_then(|s| {
                if s.type_() == SymbolType::External && *self.rows[&s].constant.as_ref() != 0.0 {
                    let v = self.var_for_symbol[&s].clone();
                    self.var_changed(v);
                }
                self.rows
                    .remove(&s)
                    .map(|r| (s, r))
            })
    }

    /// Remove the effects of a constraint on the objective function.
    fn remove_constraint_effects(&mut self, cn: &Constraint<T>, tag: &Tag) {
        if tag.marker.type_() == SymbolType::Error {
            self.remove_marker_effects(tag.marker, cn.strength());
        } else if tag.other.type_() == SymbolType::Error {
            self.remove_marker_effects(tag.other, cn.strength());
        }
    }

    /// Remove the effects of an error marker on the objective function.
    fn remove_marker_effects(&mut self, marker: Symbol, strength: f64) {
        print_inc("objective:in remove_marker_effects");
        if let Some(row) = self.rows.get(&marker) {
            self.objective.as_mut().expect("Could not get objective remove_marker_effects 1").insert_row(row, -strength);
        } else {
            self.objective.as_mut().expect("Could not get objective remove_marker_effects 2").insert_symbol(marker, -strength);
        }
        print_dec("objective:out remove_marker_effects");
    }

    /// Get the stored value for a variable.
    ///
    /// Normally values should be retrieved and updated using `fetch_changes`, but
    /// this method can be used for debugging or testing.
    pub fn get_value(&self, v: T) -> f64 {
        self.var_data.get(&v).and_then(|s| {
            self.rows.get(&s.1).map(|r| r.constant)
        })
            .map(|o| o.into_inner())
            .unwrap_or(0.0)
    }
}
