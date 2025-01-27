//! Module containing the central solving infrastructure.

pub(crate) mod engine;
pub(crate) mod initialization_context;
pub(crate) mod poster;
pub(crate) mod value;
pub(crate) mod view;

use std::fmt;

use delegate::delegate;
use itertools::Itertools;
use pindakaas::{
	solver::{
		cadical::PropagatingCadical,
		propagation::{PropagatingSolver, WithPropagator},
		LearnCallback, SlvTermSignal, SolveResult as SatSolveResult, TermCallback,
	},
	Cnf, Lit as RawLit, Valuation as SatValuation,
};
use poster::BrancherPoster;
use tracing::{debug, trace};

use crate::{
	actions::{DecisionActions, ExplanationActions, InspectionActions, TrailingActions},
	solver::{
		engine::{
			int_var::{IntVarRef, LazyLitDef, OrderStorage},
			trace_new_lit,
			trail::TrailedInt,
			Engine, PropRef, SearchStatistics,
		},
		initialization_context::{InitRef, InitializationContext},
		poster::Poster,
		value::{AssumptionChecker, NoAssumptions, Valuation, Value},
		view::{BoolViewInner, IntView, IntViewInner, SolverView},
	},
	BoolView, IntVal, LitMeaning, ReformulationError,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// Type of the optimization objective
pub enum Goal {
	/// Maximize the value of the given objective
	Maximize,
	/// Minimize the value of the given objective
	Minimize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// Statistics related to the initialization of the solver
pub struct InitStatistics {
	// TODO
	// /// Number of (non-view) boolean variables present in the solver
	// bool_vars: usize,
	/// Number of (non-view) integer variables represented in the solver
	int_vars: usize,
	/// Number of propagators in the solver
	propagators: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// Result of a solving attempt
pub enum SolveResult {
	/// The solver has found a solution.
	Satisfied,
	/// The solver has proven that the problem is unsatisfiable.
	Unsatisfiable,
	/// The solver that no more/better solutions can be found.
	Complete,
	/// The solver was interrupted before a result could be reached.
	Unknown,
}

#[derive(Clone)]
/// The main solver object that is used to interact with the LCG solver.
pub struct Solver<Oracle = PropagatingCadical<Engine>> {
	/// The inner solver that has been extended with the propagation [`Engine`]
	/// object.
	pub(crate) oracle: Oracle,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
/// Structure holding the options using to configure the solver during its
/// initialization.
pub(crate) struct SolverConfiguration {
	/// Switch between the activity-based search heuristic and the user-specific search heuristic after each restart.
	///
	/// This option is ignored if [`vsids_only`] is set to `true`.
	toggle_vsids: bool,
	/// Switch to the activity-based search heuristic after the given number of conflicts.
	///
	/// This option is ignored if [`toggle_vsids`] or [`vsids_only`] is set to `true`.
	vsids_after: Option<u32>,
	/// Only use the activity-based search heuristic provided by the SAT solver. Ignore the user-specific search heuristic.
	vsids_only: bool,
}

fn trace_learned_clause(clause: &mut dyn Iterator<Item = RawLit>) {
	debug!(clause = ?clause.map(i32::from).collect::<Vec<i32>>(), "learn clause");
}

impl InitStatistics {
	/// Number of integer variables present in the solver
	pub fn int_vars(&self) -> usize {
		self.int_vars
	}
	/// Number of propagators present in the solver
	pub fn propagators(&self) -> usize {
		self.propagators
	}
}

impl<Oracle> Solver<Oracle>
where
	Oracle: PropagatingSolver<Engine>,
	Oracle::Slv: LearnCallback,
{
	/// Set a callback function used to extract learned clauses up to a given
	/// length from the solver.
	///
	/// # Warning
	///
	/// Subsequent calls to this method override the previously set
	/// callback function.
	pub fn set_learn_callback<F: FnMut(&mut dyn Iterator<Item = RawLit>) + 'static>(
		&mut self,
		cb: Option<F>,
	) {
		if let Some(mut f) = cb {
			self.oracle.solver_mut().set_learn_callback(Some(
				move |clause: &mut dyn Iterator<Item = RawLit>| {
					trace_learned_clause(clause);
					f(clause);
				},
			));
		} else {
			self.oracle
				.solver_mut()
				.set_learn_callback(Some(trace_learned_clause));
		}
	}
}

impl<Oracle> Solver<Oracle>
where
	Oracle: PropagatingSolver<Engine>,
	Oracle::Slv: TermCallback,
{
	delegate! {
		to self.oracle.solver_mut() {
			/// Set a callback function used to indicate a termination requirement to the
			/// solver.
			///
			/// The solver will periodically call this function and check its return value
			/// during the search. Subsequent calls to this method override the previously
			/// set callback function.
			///
			/// # Warning
			///
			/// Subsequent calls to this method override the previously set
			/// callback function.
			pub fn set_terminate_callback<F: FnMut() -> SlvTermSignal + 'static>(&mut self, cb: Option<F>);
		}
	}
}

impl<Oracle: PropagatingSolver<Engine>> Solver<Oracle> {
	/// Add a brancher to the solver.
	///
	/// This method is called as part of the reformulation process of
	/// [`crate::Model`] to [`Solver`]. This method accepts a [`BrancherPoster`]
	/// implementation that is used to finalize the brancher and subscribe it to
	/// any relevant variables.
	///
	/// Note that during the search process the branchers will be asked for
	/// decisions in the order they were added to the solver.
	pub(crate) fn add_brancher<P: BrancherPoster>(&mut self, poster: P) {
		let mut actions = InitializationContext {
			slv: self,
			init_ref: InitRef::Brancher,
		};
		let brancher = poster.post(&mut actions);
		self.engine_mut().branchers.push(brancher);
	}

	#[doc(hidden)]
	/// Add a clause to the solver
	pub fn add_clause<I: IntoIterator<Item = BoolView>>(
		&mut self,
		iter: I,
	) -> Result<(), ReformulationError> {
		let mut clause = Vec::new();
		for lit in iter {
			match lit.0 {
				BoolViewInner::Lit(l) => clause.push(l),
				BoolViewInner::Const(true) => return Ok(()),
				BoolViewInner::Const(false) => {}
			}
		}
		self.oracle
			.add_clause(clause)
			.map_err(|_| ReformulationError::TrivialUnsatisfiable)
	}

	#[doc(hidden)]
	/// Method used to add a no-good clause from a solution. This clause can be
	/// used to ensure that the same solution is not found again.
	///
	/// ## Warning
	/// This method will panic if the number of variables and values do not match.
	pub fn add_no_good(
		&mut self,
		vars: &[SolverView],
		vals: &[Value],
	) -> Result<(), ReformulationError> {
		let clause = vars
			.iter()
			.zip_eq(vals)
			.map(|(var, val)| match var {
				SolverView::Bool(bv) => match val {
					Value::Bool(true) => !bv,
					Value::Bool(false) => *bv,
					_ => unreachable!(),
				},
				SolverView::Int(iv) => {
					let Value::Int(val) = val.clone() else {
						unreachable!()
					};
					self.get_int_lit(*iv, LitMeaning::NotEq(val))
				}
			})
			.collect_vec();
		debug!(clause = ?clause.iter().filter_map(|&x| if let BoolView(BoolViewInner::Lit(x)) = x { Some(i32::from(x)) } else { None }).collect::<Vec<i32>>(), "add solution nogood");
		self.add_clause(clause)
	}

	/// Add a propagator to the solver.
	///
	/// This method is called as part of the reformulation process of
	/// [`crate::Model`] to [`Solver`]. This method accepts a [`Poster`]
	/// implementation that is used to finalize the propagator and subscribe it to
	/// any relevant variables.
	pub(crate) fn add_propagator<P: Poster>(
		&mut self,
		poster: P,
	) -> Result<(), ReformulationError> {
		let prop_ref = PropRef::from(self.engine().propagators.len());
		let mut actions = InitializationContext {
			slv: self,
			init_ref: InitRef::Propagator(prop_ref),
		};
		let (prop, queue_pref) = poster.post(&mut actions)?;
		let p = self.engine_mut().propagators.push(prop);
		debug_assert_eq!(prop_ref, p);
		let engine = self.engine_mut();
		let p = engine.state.propagator_priority.push(queue_pref.priority);
		debug_assert_eq!(prop_ref, p);
		let p = self.engine_mut().state.enqueued.push(false);
		debug_assert_eq!(prop_ref, p);
		if queue_pref.enqueue_on_post {
			let state = &mut self.engine_mut().state;
			state
				.propagator_queue
				.insert(state.propagator_priority[prop_ref], prop_ref);
			state.enqueued[prop_ref] = true;
		}
		Ok(())
	}

	/// Find all solutions with regard to a list of given variables.
	/// The given closure will be called for each solution found.
	///
	/// WARNING: This method will add additional clauses into the solver to prevent the same solution
	/// from being generated twice. This will make repeated use of the Solver object impossible. Note
	/// that you can clone the Solver object before calling this method to work around this
	/// limitation.
	pub fn all_solutions(
		&mut self,
		vars: &[SolverView],
		mut on_sol: impl FnMut(&dyn Valuation),
	) -> SolveResult {
		let mut num_sol = 0;
		loop {
			let mut vals = Vec::with_capacity(vars.len());
			let status = self.solve(|value| {
				num_sol += 1;
				for v in vars {
					vals.push(value(*v));
				}
				on_sol(value);
			});
			match status {
				SolveResult::Satisfied => {
					if self.add_no_good(vars, &vals).is_err() {
						return SolveResult::Complete;
					}
				}
				SolveResult::Unsatisfiable => {
					if num_sol == 0 {
						return SolveResult::Unsatisfiable;
					} else {
						return SolveResult::Complete;
					}
				}
				SolveResult::Unknown => {
					if num_sol == 0 {
						return SolveResult::Unknown;
					} else {
						return SolveResult::Satisfied;
					}
				}
				_ => unreachable!(),
			}
		}
	}

	/// Find an optimal solution with regards to the given objective and goal.
	///
	/// Note that this method uses assumptions iteratively increase the lower bound of the objective.
	/// This does not impact the state of the solver for continued use.
	pub fn branch_and_bound(
		&mut self,
		objective: IntView,
		goal: Goal,
		mut on_sol: impl FnMut(&dyn Valuation),
	) -> (SolveResult, Option<IntVal>) {
		let mut obj_curr = None;
		let obj_bound = match goal {
			Goal::Minimize => self.get_int_lower_bound(objective),
			Goal::Maximize => self.get_int_upper_bound(objective),
		};
		let mut assump = None;
		debug!(obj_bound, "start branch and bound");
		loop {
			let status = self.solve_assuming(
				assump,
				|value| {
					obj_curr = if let Value::Int(i) = value(SolverView::Int(objective)) {
						Some(i)
					} else {
						unreachable!()
					};
					on_sol(value);
				},
				|_| {},
			);
			debug!(?status, ?obj_curr, obj_bound, ?goal, "oracle solve result");
			match status {
				SolveResult::Satisfied => {
					if obj_curr == Some(obj_bound) {
						return (SolveResult::Complete, obj_curr);
					} else {
						assump = match goal {
							Goal::Minimize => Some(
								self.get_int_lit(objective, LitMeaning::Less(obj_curr.unwrap())),
							),
							Goal::Maximize => Some(self.get_int_lit(
								objective,
								LitMeaning::GreaterEq(obj_curr.unwrap() + 1),
							)),
						};
						debug!(
							lit = i32::from({
								let BoolViewInner::Lit(l) = assump.unwrap().0 else {
									unreachable!()
								};
								l
							}),
							"add objective bound"
						);
					}
				}
				SolveResult::Unsatisfiable => {
					return if obj_curr.is_none() {
						(SolveResult::Unsatisfiable, None)
					} else {
						(SolveResult::Complete, obj_curr)
					}
				}
				SolveResult::Unknown => {
					return if obj_curr.is_none() {
						(SolveResult::Unknown, None)
					} else {
						(SolveResult::Satisfied, obj_curr)
					}
				}
				SolveResult::Complete => unreachable!(),
			}
		}
	}

	/// Access the inner [`Engine`] object.
	pub(crate) fn engine(&self) -> &Engine {
		self.oracle.propagator()
	}

	/// Mutably access the inner [`Engine`] object.
	pub(crate) fn engine_mut(&mut self) -> &mut Engine {
		self.oracle.propagator_mut()
	}

	/// Wrapper function for `all_solutions` that collects all solutions and returns them in a vector
	/// of solution values.
	///
	/// WARNING: This method will add additional clauses into the solver to prevent the same solution
	/// from being generated twice. This will make repeated use of the Solver object impossible. Note
	/// that you can clone the Solver object before calling this method to work around this
	/// limitation.
	pub fn get_all_solutions(&mut self, vars: &[SolverView]) -> (SolveResult, Vec<Vec<Value>>) {
		let mut solutions = Vec::new();
		let status = self.all_solutions(vars, |sol| {
			let mut sol_vec = Vec::with_capacity(vars.len());
			for v in vars {
				sol_vec.push(sol(*v));
			}
			solutions.push(sol_vec);
		});
		(status, solutions)
	}

	#[doc(hidden)]
	/// Get the boolean view that corresponds to the given meaning of the given
	/// integer view.
	pub fn get_int_lit(&mut self, var: IntView, meaning: LitMeaning) -> BoolView {
		DecisionActions::get_int_lit(self, var, meaning)
	}

	/// Access the initilization statistics of the [`Solver`] object.
	pub fn init_statistics(&self) -> InitStatistics {
		InitStatistics {
			int_vars: self.engine().state.int_vars.len(),
			propagators: self.engine().propagators.len(),
		}
	}

	/// Deconstruct the Solver object and return the Oracle object.
	pub fn into_oracle(self) -> Oracle::Slv {
		self.oracle.into_parts().0
	}

	/// Access the search statistics for the search process up to this point.
	pub fn search_statistics(&self) -> &SearchStatistics {
		&self.engine().state.statistics
	}

	/// Try and find a solution to the problem for which the Solver was
	/// initialized.
	pub fn solve(&mut self, on_sol: impl FnMut(&dyn Valuation)) -> SolveResult {
		self.solve_assuming([], on_sol, |_| {})
	}

	/// Try and find a solution to the problem for which the Solver was
	/// initialized, given a list of Boolean assumptions.
	pub fn solve_assuming(
		&mut self,
		assumptions: impl IntoIterator<Item = BoolView>,
		mut on_sol: impl FnMut(&dyn Valuation),
		on_fail: impl FnOnce(&dyn AssumptionChecker),
	) -> SolveResult {
		// Process assumptions
		let Ok(assumptions): Result<Vec<RawLit>, _> = assumptions
			.into_iter()
			.filter_map(|bv| match bv.0 {
				BoolViewInner::Lit(lit) => Some(Ok(lit)),
				BoolViewInner::Const(true) => None,
				BoolViewInner::Const(false) => Some(Err(ReformulationError::TrivialUnsatisfiable)),
			})
			.collect()
		else {
			on_fail(&NoAssumptions);
			return SolveResult::Unsatisfiable;
		};

		let (engine, result) = self.oracle.solve_assuming(assumptions);
		let get_int_val = |engine: &Engine, iv: IntVarRef| {
			let var_def = &engine.state.int_vars[iv];
			let val = var_def.get_lower_bound(&engine.state.trail);
			debug_assert!(
				matches!(var_def.order_encoding, OrderStorage::Lazy(_))
					|| val == var_def.get_upper_bound(&engine.state.trail)
			);
			val
		};
		match result {
			SatSolveResult::Satisfied(sol) => {
				let wrapper: &dyn Valuation = &|x| match x {
					SolverView::Bool(lit) => Value::Bool(match lit.0 {
						BoolViewInner::Lit(lit) => sol.value(lit),
						BoolViewInner::Const(b) => b,
					}),
					SolverView::Int(var) => Value::Int(match var.0 {
						IntViewInner::VarRef(iv) => get_int_val(engine, iv),
						IntViewInner::Const(i) => i,
						IntViewInner::Linear {
							transformer: transform,
							var,
						} => transform.transform(get_int_val(engine, var)),
						IntViewInner::Bool { transformer, lit } => {
							transformer.transform(sol.value(lit) as IntVal)
						}
					}),
				};
				on_sol(wrapper);
				SolveResult::Satisfied
			}
			SatSolveResult::Unsatisfiable(fail) => {
				on_fail(&fail);
				SolveResult::Unsatisfiable
			}
			SatSolveResult::Unknown => SolveResult::Unknown,
		}
	}

	delegate! {
		to self.engine_mut().state {
			/// Set whether the solver should toggle between VSIDS and a user defined
			/// search strategy after every restart.
			///
			/// Note that this setting is ignored if the solver is set to use VSIDS only.
			pub fn set_toggle_vsids(&mut self, enable: bool);
			/// Set the number of conflicts after which the solver should switch to using
			/// VSIDS to make search decisions.
			pub fn set_vsids_after(&mut self, conflicts: Option<u32>);
			/// Set wether the solver should make all search decisions based on the VSIDS
			/// only.
			pub fn set_vsids_only(&mut self, enable: bool);
		}
	}
}

impl<Oracle: PropagatingSolver<Engine>> DecisionActions for Solver<Oracle> {
	fn get_intref_lit(&mut self, iv: IntVarRef, meaning: LitMeaning) -> BoolView {
		let mut clauses = Vec::new();
		let (oracle, engine) = self.oracle.access_solving();
		let var = &mut engine.state.int_vars[iv];
		let new_var = |def: LazyLitDef| {
			// Create new variable
			let v = oracle.new_var();
			trace_new_lit!(iv, def, v);
			engine.state.trail.grow_to_boolvar(v);
			engine
				.state
				.bool_to_int
				.insert_lazy(v, iv, def.meaning.clone());
			// Add clauses to define the new variable
			for cl in def.meaning.defining_clauses(
				v.into(),
				def.prev.map(Into::into),
				def.next.map(Into::into),
			) {
				trace!(clause = ?cl.iter().map(|&x| i32::from(x)).collect::<Vec<i32>>(), "add clause");
				clauses.push(cl);
			}
			v
		};
		let bv = var.bool_lit(meaning, new_var);
		for cl in clauses {
			self.oracle
				.add_clause(cl)
				.expect("functional definition cannot make the problem unsatisfiable");
		}
		bv
	}

	fn get_num_conflicts(&self) -> u64 {
		self.engine().state.statistics.conflicts()
	}
}

impl<Oracle: PropagatingSolver<Engine>> ExplanationActions for Solver<Oracle> {
	fn get_int_val_lit(&mut self, var: IntView) -> Option<BoolView> {
		let val = self.get_int_val(var)?;
		Some(self.get_int_lit(var, LitMeaning::Eq(val)))
	}

	delegate! {
		to self.engine().state {
			fn try_int_lit(&self, var: IntView, meaning: LitMeaning) -> Option<BoolView>;
		}
		to self.engine_mut().state {
			fn get_int_lit_relaxed(&mut self, var: IntView, meaning: LitMeaning) -> (BoolView, LitMeaning);
			fn get_int_lower_bound_lit(&mut self, var: IntView) -> BoolView;
			fn get_int_upper_bound_lit(&mut self, var: IntView) -> BoolView;
		}
	}
}

impl<Base, Oracle> From<&Cnf> for Solver<Oracle>
where
	Base: for<'a> From<&'a Cnf> + WithPropagator<Engine, PropSlv = Oracle> + LearnCallback,
	Oracle: PropagatingSolver<Engine, Slv = Base>,
{
	fn from(value: &Cnf) -> Self {
		let mut slv: Base = value.into();
		slv.set_learn_callback(Some(trace_learned_clause));
		let oracle = slv.with_propagator(Engine::default());
		Self { oracle }
	}
}

impl<Oracle: PropagatingSolver<Engine>> InspectionActions for Solver<Oracle> {
	delegate! {
		to self.engine().state {
			fn check_int_in_domain(&self, var: IntView, val: IntVal) -> bool;
			fn get_int_bounds(&self, var: IntView) -> (IntVal, IntVal);
			fn get_int_lower_bound(&self, var: IntView) -> IntVal;
			fn get_int_upper_bound(&self, var: IntView) -> IntVal;
			fn get_int_val(&self, var: IntView) -> Option<IntVal>;
		}
	}
}

impl<Oracle: PropagatingSolver<Engine>> TrailingActions for Solver<Oracle> {
	delegate! {
		to self.engine().state {
			fn get_bool_val(&self, bv: BoolView) -> Option<bool>;
			fn get_trailed_int(&self, x: TrailedInt) -> IntVal;
		}
		to self.engine_mut().state {
			fn set_trailed_int(&mut self, x: TrailedInt, v: IntVal) -> IntVal;
		}
	}
}

impl<Oracle: fmt::Debug + PropagatingSolver<Engine>> fmt::Debug for Solver<Oracle> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.debug_struct("Solver")
			.field("oracle", &self.oracle)
			.field("engine", self.engine())
			.finish()
	}
}
