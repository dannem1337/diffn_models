//! Contains the `InitializationContext` struct, which is used to initialize
//! branchers and propagators to a [`Solver`] and subsequently to the
//! [`Engine`].

use delegate::delegate;
use pindakaas::solver::propagation::PropagatingSolver;

use crate::{
	actions::{DecisionActions, InitializationActions, InspectionActions, TrailingActions},
	solver::{
		engine::{
			activation_list::IntPropCond, int_var::IntVarRef, trail::TrailedInt, Engine, PropRef,
		},
		view::{BoolViewInner, IntViewInner},
	},
	BoolView, IntVal, IntView, LitMeaning, Solver,
};

/// Reference to the construct that we are initializing.
pub(crate) enum InitRef {
	/// A brancher
	Brancher,
	/// A specific propagator
	Propagator(PropRef),
}

/// Wrapper around a solver that is used to initialize branchers and propagators
/// to the solver.
pub(crate) struct InitializationContext<'a, Oracle: 'a> {
	/// Reference to the construct that we are initializing.
	pub(crate) init_ref: InitRef,
	/// The solver to which we are adding the construct.
	pub(crate) slv: &'a mut Solver<Oracle>,
}

impl<'a, Oracle: PropagatingSolver<Engine>> DecisionActions for InitializationContext<'a, Oracle> {
	delegate! {
		to self.slv {
			fn get_intref_lit(&mut self, var: IntVarRef, meaning: LitMeaning) -> BoolView;
			fn get_num_conflicts(&self) -> u64;
		}
	}
}

impl<'a, Oracle: PropagatingSolver<Engine>> InitializationActions
	for InitializationContext<'a, Oracle>
{
	fn add_clause<I: IntoIterator<Item = BoolView>>(
		&mut self,
		clause: I,
	) -> Result<(), crate::ReformulationError> {
		self.slv.add_clause(clause)
	}

	fn enqueue_on_bool_change(&mut self, var: BoolView) {
		match var.0 {
			BoolViewInner::Lit(lit) => {
				self.slv.engine_mut().state.trail.grow_to_boolvar(lit.var());
				self.slv.oracle.add_observed_var(lit.var());
				if let InitRef::Propagator(prop) = self.init_ref {
					self.slv
						.engine_mut()
						.state
						.bool_activation
						.entry(lit.var())
						.or_default()
						.push(prop);
				}
			}
			BoolViewInner::Const(_) => {}
		}
	}

	fn enqueue_on_int_change(&mut self, var: IntView, condition: IntPropCond) {
		let mut subscribe_intref = |var: IntVarRef, prop, cond| {
			self.slv.engine_mut().state.int_activation[var].add(prop, cond);
		};
		match (&self.init_ref, var.0) {
			(InitRef::Propagator(prop), IntViewInner::VarRef(var)) => {
				subscribe_intref(var, *prop, condition);
			}
			(InitRef::Propagator(prop), IntViewInner::Linear { transformer, var }) => {
				let event = if transformer.positive_scale() {
					condition
				} else {
					match condition {
						IntPropCond::LowerBound => IntPropCond::UpperBound,
						IntPropCond::UpperBound => IntPropCond::LowerBound,
						_ => condition,
					}
				};
				subscribe_intref(var, *prop, event);
			}
			(_, IntViewInner::Const(_)) => {} // ignore
			(_, IntViewInner::Bool { lit, .. }) => {
				self.enqueue_on_bool_change(BoolView(BoolViewInner::Lit(lit)));
			}
			(InitRef::Brancher, _) => {} // ignore: branchers don't receive notifications, and contained literals are already observed.
		}
	}

	fn new_trailed_int(&mut self, init: IntVal) -> TrailedInt {
		self.slv.engine_mut().state.trail.track_int(init)
	}
}

impl<'a, Oracle: PropagatingSolver<Engine>> InspectionActions
	for InitializationContext<'a, Oracle>
{
	delegate! {
		to self.slv.engine().state {
			fn get_int_lower_bound(&self, var: IntView) -> IntVal;
			fn get_int_upper_bound(&self, var: IntView) -> IntVal;
			fn get_int_bounds(&self, var: IntView) -> (IntVal, IntVal);
			fn get_int_val(&self, var: IntView) -> Option<IntVal>;
			fn check_int_in_domain(&self, var: IntView, val: IntVal) -> bool;
		}
	}
}

impl<'a, Oracle: PropagatingSolver<Engine>> TrailingActions for InitializationContext<'a, Oracle> {
	delegate! {
		to self.slv.engine().state {
			fn get_bool_val(&self, bv: BoolView) -> Option<bool>;
			fn get_trailed_int(&self, x: TrailedInt) -> IntVal;
		}
		to self.slv.engine_mut().state {
			fn set_trailed_int(&mut self, x: TrailedInt, v: IntVal) -> IntVal;
		}
	}
}
