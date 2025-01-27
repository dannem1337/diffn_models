//! Module that defines the main data structures to formulate, i.e. model, a
//! problem instance to be solved.

pub(crate) mod bool;
pub(crate) mod branching;
pub(crate) mod constraint;
pub(crate) mod flatzinc;
pub(crate) mod int;
pub(crate) mod reformulate;

use std::{
	any::Any,
	collections::{HashSet, VecDeque},
	iter::repeat,
	ops::AddAssign,
};

use pindakaas::{
	solver::{cadical::Cadical, propagation::PropagatingSolver},
	ClauseDatabase, Cnf, ConditionalDatabase, Lit as RawLit, Unsatisfiable,
};
use rangelist::{IntervalIterator, RangeList};
use tracing::warn;

use crate::{
	model::{
		bool::{BoolExpr, BoolView},
		branching::Branching,
		int::{IntVar, IntVarDef, IntView},
		reformulate::{InitConfig, ReformulationError, VariableMap},
	},
	solver::engine::{
		int_var::{EncodingType, IntVar as SlvIntVar},
		Engine,
	},
	Constraint, Solver,
};

#[derive(Debug, Default)]
/// A formulation of a problem instance in terms of decisions and constraints.
pub struct Model {
	/// A base [`Cnf`] object that contains pure Boolean parts of the problem.
	pub(crate) cnf: Cnf,
	/// An list of branching strategies that will be used by created [`Solver`]
	/// instances to be used in order to make search decisions.
	branchings: Vec<Branching>,
	/// A list of constraints that have been added to the model.
	constraints: Vec<Constraint>,
	/// The definitions of the integer variables that have been created.
	int_vars: Vec<IntVarDef>,
	/// A queue of indexes of constraints that need to be propagated.
	prop_queue: VecDeque<usize>,
	/// A flag for each constraint whether it has been enqueued for propagation.
	enqueued: Vec<bool>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
/// Reference to a decision in a [`Model`].
pub enum ModelView {
	/// Reference to a Boolean decision.
	Bool(BoolView),
	/// Reference to an integer decision.
	Int(IntView),
}

impl Model {
	/// Enqueue constraint that has index `constraint` to the propagation queue.
	fn enqueue(&mut self, constraint: usize) {
		if !self.enqueued[constraint] {
			self.prop_queue.push_back(constraint);
			self.enqueued[constraint] = true;
		}
	}

	/// Create a new Boolean variable.
	pub fn new_bool_var(&mut self) -> BoolView {
		BoolView::Lit(self.cnf.new_lit())
	}

	/// Create `len` new Boolean variables.
	pub fn new_bool_vars(&mut self, len: usize) -> Vec<BoolView> {
		self.cnf
			.new_var_range(len)
			.map(|v| BoolView::Lit(v.into()))
			.collect()
	}

	/// Create a new integer variable with the given domain.
	pub fn new_int_var(&mut self, domain: RangeList<i64>) -> IntView {
		let iv = IntVar(self.int_vars.len() as u32);
		self.int_vars.push(IntVarDef::with_domain(domain));
		IntView::Var(iv)
	}

	/// Create `len` new integer variables with the given domain.
	pub fn new_int_vars(&mut self, len: usize, domain: RangeList<i64>) -> Vec<IntVar> {
		let iv = IntVar(self.int_vars.len() as u32);
		self.int_vars
			.extend(repeat(IntVarDef::with_domain(domain)).take(len));
		(0..len).map(|i| IntVar(iv.0 + i as u32)).collect()
	}

	/// Process the model to create a [`Solver`] instance that can be used to
	/// solve it.
	///
	/// This method will return a [`Solver`] instance in addition to a
	/// [`VariableMap`], which can be used to map from [`ModelView`] to
	/// [`SolverView`]. If an error occurs during the reformulation process, or if
	/// it is found to be trivially unsatisfiable, then an error will be returned.
	pub fn to_solver<Oracle: PropagatingSolver<Engine>>(
		&mut self,
		config: &InitConfig,
	) -> Result<(Solver<Oracle>, VariableMap), ReformulationError>
	where
		Solver<Oracle>: for<'a> From<&'a Cnf>,
		Oracle::Slv: 'static,
	{
		let mut map = VariableMap::default();

		// TODO: run SAT simplification
		let mut slv = Solver::<Oracle>::from(&self.cnf);
		let any_slv: &mut dyn Any = slv.oracle.solver_mut();
		if let Some(r) = any_slv.downcast_mut::<Cadical>() {
			r.set_option("restart", config.restart() as i32);
			r.set_option("vivify", config.vivification() as i32);
		} else {
			warn!("unknown solver: vivification and restart options are ignored");
		}

		while let Some(con) = self.prop_queue.pop_front() {
			self.propagate(con)?;
			self.enqueued[con] = false;
		}

		// TODO: Detect Views From Model

		// Determine encoding types for integer variables
		let eager_order = HashSet::<IntVar>::new();
		let mut eager_direct = HashSet::<IntVar>::new();

		for c in &self.constraints {
			match c {
				Constraint::AllDifferentInt(vars) => {
					for v in vars {
						if let IntView::Var(iv) | IntView::Linear(_, iv) = v {
							if self.int_vars[iv.0 as usize].domain.card() <= (vars.len() * 100 / 80)
							{
								let _ = eager_direct.insert(*iv);
							}
						}
					}
				}
				Constraint::ArrayVarIntElement(_, IntView::Var(iv) | IntView::Linear(_, iv), _) => {
					let _ = eager_direct.insert(*iv);
				}
				Constraint::TableInt(vars, _) => {
					for v in vars {
						if let IntView::Var(iv) | IntView::Linear(_, iv) = v {
							let _ = eager_direct.insert(*iv);
						}
					}
				}
				_ => {}
			}
		}

		// Create integer data structures within the solver
		for i in 0..self.int_vars.len() {
			let var = &self.int_vars[i];
			let direct_enc = if eager_direct.contains(&IntVar(i as u32)) {
				EncodingType::Eager
			} else {
				EncodingType::Lazy
			};
			let order_enc = if eager_order.contains(&IntVar(i as u32))
				|| eager_direct.contains(&IntVar(i as u32))
				|| var.domain.card() <= config.int_eager_limit()
			{
				EncodingType::Eager
			} else {
				EncodingType::Lazy
			};
			let view = SlvIntVar::new_in(&mut slv, var.domain.clone(), order_enc, direct_enc);
			map.insert_int(IntVar(i as u32), view);
		}

		// Create constraint data structures within the solver
		for c in self.constraints.iter() {
			c.to_solver(&mut slv, &mut map)?;
		}
		// Add branching data structures to the solver
		for b in self.branchings.iter() {
			b.to_solver(&mut slv, &mut map);
		}

		Ok((slv, map))
	}
}
impl AddAssign<BoolExpr> for Model {
	fn add_assign(&mut self, rhs: BoolExpr) {
		self.add_assign(Constraint::PropLogic(rhs));
	}
}

impl AddAssign<Branching> for Model {
	fn add_assign(&mut self, rhs: Branching) {
		self.branchings.push(rhs);
	}
}

impl AddAssign<Constraint> for Model {
	fn add_assign(&mut self, rhs: Constraint) {
		self.constraints.push(rhs);
		self.enqueued.push(false);
		self.enqueue(self.constraints.len() - 1);
		self.subscribe(self.constraints.len() - 1);
	}
}

impl ClauseDatabase for Model {
	type CondDB = Model;

	fn add_clause<I: IntoIterator<Item = RawLit>>(&mut self, cl: I) -> Result<(), Unsatisfiable> {
		self.cnf.add_clause(cl)
	}

	fn new_var_range(&mut self, len: usize) -> pindakaas::VarRange {
		self.cnf.new_var_range(len)
	}

	fn with_conditions(&mut self, conditions: Vec<RawLit>) -> ConditionalDatabase<Self::CondDB> {
		ConditionalDatabase::new(self, conditions)
	}
}

impl From<BoolView> for ModelView {
	fn from(value: BoolView) -> Self {
		Self::Bool(value)
	}
}

impl From<IntView> for ModelView {
	fn from(value: IntView) -> Self {
		Self::Int(value)
	}
}
