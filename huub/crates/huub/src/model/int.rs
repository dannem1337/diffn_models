//! Representation and manipulation of integer decision variable in [`Model`].

use std::ops::{Add, Mul, Neg};

use pindakaas::{solver::propagation::PropagatingSolver, ClauseDatabase};
use rangelist::{IntervalIterator, RangeList};

use crate::{
	helpers::linear_transform::LinearTransform,
	model::{bool::BoolView, reformulate::VariableMap},
	solver::{engine::Engine, view},
	IntSetVal, IntVal, LitMeaning, Model, NonZeroIntVal, ReformulationError, Solver,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// Reference type for integer decision variables in a [`Model`].
pub struct IntVar(pub(crate) u32);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Defintition of an integer decision variable in a [`Model`].
pub(crate) struct IntVarDef {
	/// The set of possible values that the variable can take.
	pub(crate) domain: IntSetVal,
	/// The list of (indexes of) constraints in which the variable appears.
	///
	/// This list is used to enqueue the constraints for propagation when the
	/// domain of the variable changes.
	pub(crate) constraints: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
/// A reference to an integer value or its transformation in a [`Model`].
pub enum IntView {
	/// Direct reference to an integer variable.
	Var(IntVar),
	/// Constant integer value.
	Const(i64),
	/// Linear transformation of an integer variable.
	Linear(LinearTransform, IntVar),
	/// Linear transformation of a Boolean variable.
	Bool(LinearTransform, BoolView),
}

impl IntVarDef {
	/// Create a new integer variable definition with the given domain.
	pub(crate) fn with_domain(dom: IntSetVal) -> Self {
		Self {
			domain: dom,
			constraints: Vec::new(),
		}
	}
}

impl IntView {
	/// Get the [`view::IntView`] to which the `IntView` will be mapped.
	pub(crate) fn to_arg<Oracle: PropagatingSolver<Engine>>(
		&self,
		slv: &mut Solver<Oracle>,
		map: &mut VariableMap,
	) -> view::IntView {
		map.get_int(slv, self)
	}
}

impl Add<IntVal> for IntView {
	type Output = Self;

	fn add(self, rhs: IntVal) -> Self::Output {
		match self {
			Self::Var(x) => Self::Linear(LinearTransform::offset(rhs), x),
			Self::Const(v) => Self::Const(v + rhs),
			Self::Linear(t, x) => Self::Linear(t + rhs, x),
			Self::Bool(t, x) => Self::Bool(t + rhs, x),
		}
	}
}

impl From<BoolView> for IntView {
	fn from(value: BoolView) -> Self {
		match value {
			BoolView::Const(b) => Self::Const(b as IntVal),
			x => Self::Bool(LinearTransform::offset(0), x),
		}
	}
}

impl From<IntVar> for IntView {
	fn from(value: IntVar) -> Self {
		Self::Var(value)
	}
}

impl Mul<IntVal> for IntView {
	type Output = Self;

	fn mul(self, rhs: IntVal) -> Self::Output {
		if rhs == 0 {
			Self::Const(0)
		} else {
			self.mul(NonZeroIntVal::new(rhs).unwrap())
		}
	}
}

impl Mul<NonZeroIntVal> for IntView {
	type Output = Self;

	fn mul(self, rhs: NonZeroIntVal) -> Self::Output {
		match self {
			Self::Var(x) => Self::Linear(LinearTransform::scaled(rhs), x),
			Self::Const(v) => Self::Const(v * rhs.get()),
			Self::Linear(t, x) => Self::Linear(t * rhs, x),
			Self::Bool(t, x) => Self::Bool(t * rhs, x),
		}
	}
}

impl Neg for IntView {
	type Output = Self;

	fn neg(self) -> Self::Output {
		match self {
			Self::Var(x) => {
				Self::Linear(LinearTransform::scaled(NonZeroIntVal::new(-1).unwrap()), x)
			}
			Self::Const(v) => Self::Const(-v),
			Self::Linear(t, x) => Self::Linear(-t, x),
			Self::Bool(t, x) => Self::Bool(-t, x),
		}
	}
}

impl Model {
	/// Check whether a given integer is within the set of possible values that a
	/// given integer view can take.
	pub(crate) fn check_int_in_domain(&self, iv: &IntView, val: IntVal) -> bool {
		match iv {
			IntView::Var(v) => self.int_vars[v.0 as usize].domain.contains(&val),
			IntView::Const(v) => *v == val,
			IntView::Linear(t, v) => match t.rev_transform_lit(LitMeaning::Eq(val)) {
				Ok(LitMeaning::Eq(val)) => self.int_vars[v.0 as usize].domain.contains(&val),
				Err(false) => false,
				_ => unreachable!(),
			},
			IntView::Bool(t, _) => match t.rev_transform_lit(LitMeaning::Eq(val)) {
				Ok(LitMeaning::Eq(val)) => val == 0 || val == 1,
				Err(false) => false,
				_ => unreachable!(),
			},
		}
	}

	/// Ensure that a given integer view cannot take any of the values in the
	/// given set.
	pub(crate) fn diff_int_domain(
		&mut self,
		iv: &IntView,
		mask: &IntSetVal,
		con: usize,
	) -> Result<(), ReformulationError> {
		match iv {
			IntView::Var(v) => {
				let diff: RangeList<_> = self.int_vars[v.0 as usize].domain.diff(mask);
				if diff.is_empty() {
					return Err(ReformulationError::TrivialUnsatisfiable);
				} else if self.int_vars[v.0 as usize].domain == diff {
					return Ok(());
				}
				self.int_vars[v.0 as usize].domain = diff;
				let constraints = self.int_vars[v.0 as usize].constraints.clone();
				for c in constraints {
					if c != con {
						self.enqueue(c);
					}
				}
				Ok(())
			}
			IntView::Const(v) => {
				if mask.contains(v) {
					Err(ReformulationError::TrivialUnsatisfiable)
				} else {
					Ok(())
				}
			}
			IntView::Linear(trans, iv) => {
				let mask = trans.rev_transform_int_set(mask);
				self.diff_int_domain(&IntView::Var(*iv), &mask, con)
			}
			IntView::Bool(trans, b) => {
				let mask = trans.rev_transform_int_set(mask);
				if mask.contains(&0) {
					self.set_bool(b, con)?;
				}
				if mask.contains(&1) {
					self.set_bool(&!b, con)?;
				}
				Ok(())
			}
		}
	}

	/// Return the minimal value that the given integer view can take.
	pub(crate) fn get_int_lower_bound(&self, iv: &IntView) -> IntVal {
		match *iv {
			IntView::Var(v) => {
				let def = &self.int_vars[v.0 as usize];
				*def.domain.lower_bound().unwrap()
			}
			IntView::Const(v) => v,
			IntView::Linear(t, v) => {
				let def = &self.int_vars[v.0 as usize];
				if t.positive_scale() {
					t.transform(*def.domain.lower_bound().unwrap())
				} else {
					t.transform(*def.domain.upper_bound().unwrap())
				}
			}
			IntView::Bool(t, _) => {
				if t.positive_scale() {
					t.transform(0)
				} else {
					t.transform(1)
				}
			}
		}
	}

	/// Return the maximal value that the given integer view can take.
	pub(crate) fn get_int_upper_bound(&self, iv: &IntView) -> IntVal {
		match *iv {
			IntView::Var(v) => {
				let def = &self.int_vars[v.0 as usize];
				*def.domain.upper_bound().unwrap()
			}
			IntView::Const(v) => v,
			IntView::Linear(t, v) => {
				let def = &self.int_vars[v.0 as usize];
				if t.positive_scale() {
					t.transform(*def.domain.upper_bound().unwrap())
				} else {
					t.transform(*def.domain.lower_bound().unwrap())
				}
			}
			IntView::Bool(t, _) => {
				if t.positive_scale() {
					t.transform(1)
				} else {
					t.transform(0)
				}
			}
		}
	}

	/// Ensure that the given integer decision variable takes a value in in the
	/// given set.
	pub(crate) fn intersect_int_domain(
		&mut self,
		iv: &IntView,
		mask: &IntSetVal,
		con: usize,
	) -> Result<(), ReformulationError> {
		match iv {
			IntView::Var(v) => {
				let intersect: RangeList<_> = self.int_vars[v.0 as usize].domain.intersect(mask);
				if intersect.is_empty() {
					return Err(ReformulationError::TrivialUnsatisfiable);
				} else if self.int_vars[v.0 as usize].domain == intersect {
					return Ok(());
				}
				self.int_vars[v.0 as usize].domain = intersect;
				let constraints = self.int_vars[v.0 as usize].constraints.clone();
				for c in constraints {
					if c != con {
						self.enqueue(c);
					}
				}
				Ok(())
			}
			IntView::Const(v) => {
				if !mask.contains(v) {
					Err(ReformulationError::TrivialUnsatisfiable)
				} else {
					Ok(())
				}
			}
			IntView::Linear(trans, iv) => {
				let mask = trans.rev_transform_int_set(mask);
				self.intersect_int_domain(&IntView::Var(*iv), &mask, con)
			}
			IntView::Bool(trans, b) => {
				let mask = trans.rev_transform_int_set(mask);
				if !mask.contains(&0) {
					self.set_bool(b, con)?;
				}
				if !mask.contains(&1) {
					self.set_bool(&!b, con)?;
				}
				Ok(())
			}
		}
	}

	/// Set the value of a boolean variable.
	pub(crate) fn set_bool(&mut self, b: &BoolView, con: usize) -> Result<(), ReformulationError> {
		match b {
			BoolView::Lit(l) => self
				.add_clause([*l])
				.map_err(|_| ReformulationError::TrivialUnsatisfiable),
			BoolView::Const(true) => Ok(()),
			BoolView::Const(false) => Err(ReformulationError::TrivialUnsatisfiable),
			BoolView::IntEq(iv, val) => self.set_int_value(iv, *val, con),
			BoolView::IntGreater(iv, val) => self.set_int_lower_bound(iv, val + 1, con),
			BoolView::IntGreaterEq(iv, val) => self.set_int_lower_bound(iv, *val, con),
			BoolView::IntLess(iv, val) => self.set_int_upper_bound(iv, val - 1, con),
			BoolView::IntLessEq(iv, val) => self.set_int_upper_bound(iv, *val, con),
			BoolView::IntNotEq(iv, val) => {
				self.diff_int_domain(iv, &RangeList::from(*val..=*val), con)
			}
		}
	}

	/// Ensure that a given integer variable cannot take a value lower than `lb`.
	pub(crate) fn set_int_lower_bound(
		&mut self,
		iv: &IntView,
		lb: IntVal,
		con: usize,
	) -> Result<(), ReformulationError> {
		match iv {
			IntView::Var(v) => {
				let def = &mut self.int_vars[v.0 as usize];
				if lb <= *def.domain.lower_bound().unwrap() {
					return Ok(());
				} else if lb > *def.domain.upper_bound().unwrap() {
					return Err(ReformulationError::TrivialUnsatisfiable);
				}
				def.domain = RangeList::from_iter(def.domain.iter().filter_map(|r| {
					if *r.end() < lb {
						None
					} else if *r.start() < lb {
						Some(lb..=*r.end())
					} else {
						Some(r)
					}
				}));
				let constraints = def.constraints.clone();
				for c in constraints {
					if c != con {
						self.enqueue(c);
					}
				}
				Ok(())
			}
			IntView::Const(v) => {
				if *v < lb {
					Err(ReformulationError::TrivialUnsatisfiable)
				} else {
					Ok(())
				}
			}
			IntView::Linear(trans, iv) => {
				match trans.rev_transform_lit(LitMeaning::GreaterEq(lb)) {
					Ok(LitMeaning::GreaterEq(val)) => {
						self.set_int_lower_bound(&IntView::Var(*iv), val, con)
					}
					Ok(LitMeaning::Less(val)) => {
						self.set_int_upper_bound(&IntView::Var(*iv), val - 1, con)
					}
					_ => unreachable!(),
				}
			}
			IntView::Bool(trans, b) => match trans.rev_transform_lit(LitMeaning::GreaterEq(lb)) {
				Ok(LitMeaning::GreaterEq(1)) => self.set_bool(b, con),
				Ok(LitMeaning::GreaterEq(val)) if val >= 2 => {
					Err(ReformulationError::TrivialUnsatisfiable)
				}
				Ok(LitMeaning::GreaterEq(_)) => Ok(()),
				Ok(LitMeaning::Less(1)) => self.set_bool(&!b, con),
				Ok(LitMeaning::Less(val)) if val <= 0 => {
					Err(ReformulationError::TrivialUnsatisfiable)
				}
				Ok(LitMeaning::Less(_)) => Ok(()),
				_ => unreachable!(),
			},
		}
	}

	/// Ensure that an integer variable cannot take a value greater than `ub`.
	pub(crate) fn set_int_upper_bound(
		&mut self,
		iv: &IntView,
		ub: IntVal,
		con: usize,
	) -> Result<(), ReformulationError> {
		match iv {
			IntView::Var(v) => {
				let def = &mut self.int_vars[v.0 as usize];
				if ub >= *def.domain.upper_bound().unwrap() {
					return Ok(());
				} else if ub < *def.domain.lower_bound().unwrap() {
					return Err(ReformulationError::TrivialUnsatisfiable);
				}
				def.domain = RangeList::from_iter(def.domain.iter().filter_map(|r| {
					if ub < *r.start() {
						None
					} else if ub < *r.end() {
						Some(*r.start()..=ub)
					} else {
						Some(r)
					}
				}));
				let constraints = def.constraints.clone();
				for c in constraints {
					if c != con {
						self.enqueue(c);
					}
				}
				Ok(())
			}
			IntView::Const(v) => {
				if *v > ub {
					Err(ReformulationError::TrivialUnsatisfiable)
				} else {
					Ok(())
				}
			}
			IntView::Linear(trans, iv) => match trans.rev_transform_lit(LitMeaning::Less(ub + 1)) {
				Ok(LitMeaning::GreaterEq(val)) => {
					self.set_int_lower_bound(&IntView::Var(*iv), val, con)
				}
				Ok(LitMeaning::Less(val)) => {
					self.set_int_upper_bound(&IntView::Var(*iv), val - 1, con)
				}
				_ => unreachable!(),
			},
			IntView::Bool(trans, b) => match trans.rev_transform_lit(LitMeaning::Less(ub + 1)) {
				Ok(LitMeaning::GreaterEq(1)) => self.set_bool(b, con),
				Ok(LitMeaning::GreaterEq(val)) if val >= 2 => {
					Err(ReformulationError::TrivialUnsatisfiable)
				}
				Ok(LitMeaning::GreaterEq(_)) => Ok(()),
				Ok(LitMeaning::Less(1)) => self.set_bool(&!b, con),
				Ok(LitMeaning::Less(val)) if val <= 0 => {
					Err(ReformulationError::TrivialUnsatisfiable)
				}
				Ok(LitMeaning::Less(_)) => Ok(()),
				_ => unreachable!(),
			},
		}
	}

	/// Set the value of an integer decision variable.
	pub(crate) fn set_int_value(
		&mut self,
		iv: &IntView,
		val: IntVal,
		con: usize,
	) -> Result<(), ReformulationError> {
		match iv {
			IntView::Var(v) => {
				let def = &mut self.int_vars[v.0 as usize];
				if def.domain.contains(&val) {
					def.domain = RangeList::from(val..=val);
					let constraints = def.constraints.clone();
					for c in constraints {
						if c != con {
							self.enqueue(c);
						}
					}
					Ok(())
				} else {
					Err(ReformulationError::TrivialUnsatisfiable)
				}
			}
			IntView::Const(i) if *i == val => Ok(()),
			IntView::Const(_) => Err(ReformulationError::TrivialUnsatisfiable),
			IntView::Linear(trans, iv) => match trans.rev_transform_lit(LitMeaning::Eq(val)) {
				Ok(LitMeaning::Eq(val)) => self.set_int_value(&IntView::Var(*iv), val, con),
				Err(b) => {
					debug_assert!(!b);
					Err(ReformulationError::TrivialUnsatisfiable)
				}
				_ => unreachable!(),
			},
			IntView::Bool(trans, b) => match trans.rev_transform_lit(LitMeaning::Eq(val)) {
				Ok(LitMeaning::Eq(val)) => match val {
					0 => self.set_bool(&!b, con),
					1 => self.set_bool(b, con),
					_ => Err(ReformulationError::TrivialUnsatisfiable),
				},
				Err(b) => {
					debug_assert!(!b);
					Err(ReformulationError::TrivialUnsatisfiable)
				}
				_ => unreachable!(),
			},
		}
	}
}
