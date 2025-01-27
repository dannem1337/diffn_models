//! Traits that define different sets of actions that can be performed at
//! different phases of the solving process.

use crate::{
	propagator::{Conflict, LazyReason, ReasonBuilder},
	solver::{
		engine::{activation_list::IntPropCond, int_var::IntVarRef, trail::TrailedInt},
		view::{BoolViewInner, IntViewInner},
	},
	BoolView, IntVal, IntView, LitMeaning, ReformulationError,
};

/// Actions that can be performed by a [`Brancher`] when making search
/// decisions.
pub(crate) trait DecisionActions: InspectionActions {
	/// Get (or create) a literal for the given integer view with the given meaning.
	fn get_int_lit(&mut self, var: IntView, mut meaning: LitMeaning) -> BoolView {
		{
			if let IntViewInner::Linear { transformer, .. }
			| IntViewInner::Bool { transformer, .. } = var.0
			{
				match transformer.rev_transform_lit(meaning) {
					Ok(m) => meaning = m,
					Err(v) => return BoolView(BoolViewInner::Const(v)),
				}
			}

			match var.0 {
				IntViewInner::VarRef(var) | IntViewInner::Linear { var, .. } => {
					self.get_intref_lit(var, meaning)
				}
				IntViewInner::Const(c) => BoolView(BoolViewInner::Const(match meaning {
					LitMeaning::Eq(i) => c == i,
					LitMeaning::NotEq(i) => c != i,
					LitMeaning::GreaterEq(i) => c >= i,
					LitMeaning::Less(i) => c < i,
				})),
				IntViewInner::Bool { lit, .. } => {
					let (meaning, negated) =
						if matches!(meaning, LitMeaning::NotEq(_) | LitMeaning::Less(_)) {
							(!meaning, true)
						} else {
							(meaning, false)
						};
					let bv = BoolView(match meaning {
						LitMeaning::Eq(0) => BoolViewInner::Lit(!lit),
						LitMeaning::Eq(1) => BoolViewInner::Lit(lit),
						LitMeaning::Eq(_) => BoolViewInner::Const(false),
						LitMeaning::GreaterEq(1) => BoolViewInner::Lit(lit),
						LitMeaning::GreaterEq(i) if i > 1 => BoolViewInner::Const(false),
						LitMeaning::GreaterEq(_) => BoolViewInner::Const(true),
						_ => unreachable!(),
					});
					if negated {
						!bv
					} else {
						bv
					}
				}
			}
		}
	}

	/// Get (or create) a literal for the given referenced integer variable with the given meaning.
	fn get_intref_lit(&mut self, var: IntVarRef, meaning: LitMeaning) -> BoolView;

	/// Returns the number of conflicts up to this point in the search process.
	fn get_num_conflicts(&self) -> u64;
}

/// Actions that can be performed when explaining a propagation that was
/// performed.
pub(crate) trait ExplanationActions: InspectionActions {
	/// Get a Boolean view that represents the given meaning (that is currently
	/// `true`) on the integer view, if it already exists.
	fn try_int_lit(&self, var: IntView, meaning: LitMeaning) -> Option<BoolView>;

	/// Get a Boolean view that represents the given meaning (that is currently
	/// `true`) on the integer view, or a relaxation if the literal does not yet
	/// exist.
	fn get_int_lit_relaxed(&mut self, var: IntView, meaning: LitMeaning) -> (BoolView, LitMeaning);

	/// Get the Boolean view that represents the current assignment of the integer
	/// view, or `None` if the integer view is not assigned.
	fn get_int_val_lit(&mut self, var: IntView) -> Option<BoolView>;

	/// Get the Boolean view that represents that the integer view will take a
	/// value greater or equal to its current lower bound.
	fn get_int_lower_bound_lit(&mut self, var: IntView) -> BoolView;

	/// Get the Boolean view that represents that the integer view will take a
	/// value less or equal to its current upper bound.
	fn get_int_upper_bound_lit(&mut self, var: IntView) -> BoolView;
}

/// Actions that can be performed during the initlization of propagators and
/// branchers.
pub(crate) trait InitializationActions: DecisionActions {
	/// Add a clause to the solver.
	fn add_clause<I: IntoIterator<Item = BoolView>>(
		&mut self,
		clause: I,
	) -> Result<(), ReformulationError>;

	/// Create a new trailed integer value with the given initial value.
	fn new_trailed_int(&mut self, init: IntVal) -> TrailedInt;

	/// Enqueue a propagator to be enqueued when a boolean variable is assigned.
	fn enqueue_on_bool_change(&mut self, var: BoolView);

	/// Enqueue a propagator to be enqueued when an integer variable is changed
	/// according to the given propagation condition.
	fn enqueue_on_int_change(&mut self, var: IntView, condition: IntPropCond);
}

/// Actions that can generally be performed when the solver is (partially)
/// initialized.
pub(crate) trait InspectionActions: TrailingActions {
	/// Get the minimum value that an integer view is guaranteed to take (given
	/// the current search decisions).
	fn get_int_lower_bound(&self, var: IntView) -> IntVal;

	/// Get the maximum value that an integer view is guaranteed to take (given
	/// the current search decisions).
	fn get_int_upper_bound(&self, var: IntView) -> IntVal;

	/// Convenience method to get both the lower and upper bounds of an integer
	/// view.
	fn get_int_bounds(&self, var: IntView) -> (IntVal, IntVal) {
		(self.get_int_lower_bound(var), self.get_int_upper_bound(var))
	}

	/// Get the current value of an integer view, if it has been assigned.
	fn get_int_val(&self, var: IntView) -> Option<IntVal> {
		let (lb, ub) = self.get_int_bounds(var);
		if lb == ub {
			Some(lb)
		} else {
			None
		}
	}

	/// Check whether a given integer view can take a given value (given the
	/// current search decisions).
	fn check_int_in_domain(&self, var: IntView, val: IntVal) -> bool;
}

/// Actions that can be performed during propagation.
pub(crate) trait PropagationActions: ExplanationActions + DecisionActions {
	/// Enforce a boolean view to be `true` because of a given `reason`.
	///
	/// Note that it is possible to enforce that a boolean view is `false` by
	/// negating the view, i.e. `!bv`.
	fn set_bool(&mut self, bv: BoolView, reason: impl ReasonBuilder<Self>) -> Result<(), Conflict>;

	/// Enforce that a an integer view takes a value that is greater or equal to
	/// `val` because of the given `reason`.
	fn set_int_lower_bound(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict>;

	/// Enforce that a an integer view takes a value that is less or equal to
	/// `val` because of the given `reason`.
	fn set_int_upper_bound(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict>;

	#[expect(dead_code, reason = "TODO: no current use case in propagators")]
	/// Enforce that a an integer view takes a value `val` because of the given
	/// `reason`.
	fn set_int_val(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict>;

	/// Enforce that a an integer view cannot take a value `val` because of the
	/// given `reason`.
	fn set_int_not_eq(
		&mut self,
		var: IntView,
		val: IntVal,
		reason: impl ReasonBuilder<Self>,
	) -> Result<(), Conflict>;

	/// Create a placeholder reason that will cause the solver to call the
	/// propagator's [`Propagator::explain`] method when the reason is needed.
	fn deferred_reason(&self, data: u64) -> LazyReason;
}

/// Basic actions that can be performed when the trailing infrastructure is
/// available.
pub(crate) trait TrailingActions {
	/// Get the current value of a [`BoolView`], if it has been assigned.
	fn get_bool_val(&self, bv: BoolView) -> Option<bool>;
	/// Get the current value of a [`TrailedInt`].
	fn get_trailed_int(&self, i: TrailedInt) -> IntVal;
	/// Change the value of a [`TrailedInt`] in a way that can be undone if the
	/// solver backtracks to a previous state.
	fn set_trailed_int(&mut self, i: TrailedInt, v: IntVal) -> IntVal;
}
