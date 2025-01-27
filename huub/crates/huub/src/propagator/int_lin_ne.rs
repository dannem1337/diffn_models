//! Propagator for the `int_lin_ne` constraint, and its reification. This
//! constraint enforce that the sum of the products of the variables is not
//! equal to a given value.

use pindakaas::Lit as RawLit;

use crate::{
	actions::InitializationActions,
	helpers::opt_field::OptField,
	propagator::{Conflict, ExplanationActions, PropagationActions, Propagator, ReasonBuilder},
	solver::{
		engine::{activation_list::IntPropCond, queue::PriorityLevel, trail::TrailedInt},
		poster::{BoxedPropagator, Poster, QueuePreferences},
		value::IntVal,
		view::{BoolViewInner, IntView, IntViewInner},
	},
	BoolView, ReformulationError,
};

/// Type alias for the reified version of the [`IntLinearNotEqValueImpl`]
/// propagator.
pub(crate) type IntLinearNotEqImpValue = IntLinearNotEqValueImpl<1>;

/// Type alias for the non-reified version of the [`IntLinearNotEqValueImpl`]
/// propagator.
pub(crate) type IntLinearNotEqValue = IntLinearNotEqValueImpl<0>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Value consistent propagator for the `int_lin_ne` or `int_lin_ne_imp`
/// constraint.
///
/// `R` should be `0` if the propagator is not refied, or `1` if it is. Other
/// values are invalid.
pub(crate) struct IntLinearNotEqValueImpl<const R: usize> {
	/// Variables in the sumation
	vars: Vec<IntView>,
	/// The value the sumation should not equal
	violation: IntVal,
	/// Reified variable, if any
	reification: OptField<R, RawLit>,
	/// Number of variables currently fixed
	num_fixed: TrailedInt,
}

/// [`Poster`] for a the [`IntLinearNotEqValue`] or [`IntLinearNotEqImpValue`]
/// propagator.
struct IntLinearNotEqValuePoster<const R: usize> {
	/// Variables in the sumation
	vars: Vec<IntView>,
	/// Value that the sum of the variables must not equal.
	val: IntVal,
	/// Optional reification variable implying the constraint.
	reification: OptField<R, RawLit>,
}

impl IntLinearNotEqImpValue {
	/// Prepare the [`IntLinearNotEqImpValue`] propagator to be posted to the
	/// solver.
	pub(crate) fn prepare<V: Into<IntView>, VI: IntoIterator<Item = V>>(
		vars: VI,
		mut val: IntVal,
		r: RawLit,
	) -> impl Poster {
		IntLinearNotEqValuePoster::<1> {
			vars: vars
				.into_iter()
				.filter_map(|v| {
					let v = v.into();
					if let IntViewInner::Const(c) = v.0 {
						val -= c;
						None
					} else {
						Some(v)
					}
				})
				.collect(),
			val,
			reification: OptField::new(r),
		}
	}
}

impl IntLinearNotEqValue {
	/// Prepare the [`IntLinearNotEqValue`] propagator to be posted to the
	/// solver.
	pub(crate) fn prepare<V: Into<IntView>, VI: IntoIterator<Item = V>>(
		vars: VI,
		mut val: IntVal,
	) -> impl Poster {
		IntLinearNotEqValuePoster::<0> {
			vars: vars
				.into_iter()
				.filter_map(|v| {
					let v = v.into();
					if let IntViewInner::Const(c) = v.0 {
						val -= c;
						None
					} else {
						Some(v)
					}
				})
				.collect(),
			val,
			reification: Default::default(),
		}
	}
}

impl<const R: usize> IntLinearNotEqValueImpl<R> {
	/// Helper function to construct the reason for propagation given the index of
	/// the variable in the list of variables to sum or the length of the list, if
	/// explaining the reification.
	fn reason<A: ExplanationActions>(&self, data: usize) -> impl ReasonBuilder<A> + '_ {
		move |actions: &mut A| {
			let mut conj: Vec<_> = self
				.vars
				.iter()
				.enumerate()
				.filter_map(|(i, v)| {
					if data != i {
						Some(actions.get_int_val_lit(*v).unwrap())
					} else {
						None
					}
				})
				.collect();
			if let Some(&r) = self.reification.get() {
				if data != self.vars.len() {
					conj.push(BoolView(BoolViewInner::Lit(r)));
				}
			}
			conj
		}
	}
}

impl<const R: usize, P, E> Propagator<P, E> for IntLinearNotEqValueImpl<R>
where
	P: PropagationActions,
	E: ExplanationActions,
{
	#[tracing::instrument(name = "int_lin_ne", level = "trace", skip(self, actions))]
	fn propagate(&mut self, actions: &mut P) -> Result<(), Conflict> {
		let (r, r_fixed) = if let Some(r) = self.reification.get() {
			let r_bv = BoolView(BoolViewInner::Lit(*r));
			match actions.get_bool_val(r_bv) {
				Some(false) => return Ok(()),
				Some(true) => (r_bv, true),
				None => (r_bv, false),
			}
		} else {
			(true.into(), true)
		};
		let mut sum = 0;
		let mut unfixed = None;
		for (i, v) in self.vars.iter().enumerate() {
			if let Some(val) = actions.get_int_val(*v) {
				sum += val;
			} else if unfixed.is_some() {
				return Ok(());
			} else {
				unfixed = Some((i, v));
			}
		}
		if let Some((i, v)) = unfixed {
			if !r_fixed {
				return Ok(());
			}
			let val = self.violation - sum;
			actions.set_int_not_eq(*v, val, self.reason(i))
		} else if sum == self.violation {
			actions.set_bool(!r, self.reason(self.vars.len()))
		} else {
			Ok(())
		}
	}
}

impl<const R: usize> Poster for IntLinearNotEqValuePoster<R> {
	fn post<I: InitializationActions>(
		self,
		actions: &mut I,
	) -> Result<(BoxedPropagator, QueuePreferences), ReformulationError> {
		let prop = IntLinearNotEqValueImpl {
			vars: self.vars,
			violation: self.val,
			reification: self.reification,
			num_fixed: actions.new_trailed_int(0),
		};
		for &v in prop.vars.iter() {
			actions.enqueue_on_int_change(v, IntPropCond::Fixed);
		}
		if let Some(r) = prop.reification.get() {
			actions.enqueue_on_bool_change(BoolView(BoolViewInner::Lit(*r)));
		}
		Ok((
			Box::new(prop),
			QueuePreferences {
				enqueue_on_post: false,
				priority: PriorityLevel::Low,
			},
		))
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use pindakaas::{solver::cadical::PropagatingCadical, Cnf};
	use rangelist::RangeList;
	use tracing_test::traced_test;

	use crate::{
		propagator::int_lin_ne::IntLinearNotEqValue,
		solver::engine::int_var::{EncodingType, IntVar},
		Constraint, InitConfig, Model, NonZeroIntVal, Solver,
	};

	#[test]
	#[traced_test]
	fn test_linear_ne_sat() {
		let mut slv = Solver::<PropagatingCadical<_>>::from(&Cnf::default());
		let a = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let b = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);
		let c = IntVar::new_in(
			&mut slv,
			RangeList::from_iter([1..=2]),
			EncodingType::Eager,
			EncodingType::Eager,
		);

		slv.add_propagator(IntLinearNotEqValue::prepare(
			vec![a * NonZeroIntVal::new(2).unwrap(), b, c],
			6,
		))
		.unwrap();

		slv.expect_solutions(
			&[a, b, c],
			expect![[r#"
		1, 1, 1
		1, 1, 2
		1, 2, 1
		2, 1, 2
		2, 2, 1
		2, 2, 2"#]],
		);
	}

	#[test]
	#[traced_test]
	fn test_reified_linear_ne_sat() {
		let mut prb = Model::default();
		let r = prb.new_bool_var();
		let a = prb.new_int_var((1..=2).into());
		let b = prb.new_int_var((1..=2).into());
		let c = prb.new_int_var((1..=2).into());

		prb += Constraint::IntLinNotEqImp(
			vec![
				a.clone() * NonZeroIntVal::new(2).unwrap(),
				b.clone(),
				c.clone(),
			],
			6,
			r.clone().into(),
		);
		let (mut slv, map): (Solver, _) = prb.to_solver(&InitConfig::default()).unwrap();
		let a = map.get(&mut slv, &a.into());
		let b = map.get(&mut slv, &b.into());
		let c = map.get(&mut slv, &c.into());
		let r = map.get(&mut slv, &r.into());
		slv.expect_solutions(
			&[r, a, b, c],
			expect![[r#"
		false, 1, 1, 1
		false, 1, 1, 2
		false, 1, 2, 1
		false, 1, 2, 2
		false, 2, 1, 1
		false, 2, 1, 2
		false, 2, 2, 1
		false, 2, 2, 2
		true, 1, 1, 1
		true, 1, 1, 2
		true, 1, 2, 1
		true, 2, 1, 2
		true, 2, 2, 1
		true, 2, 2, 2"#]],
		);
	}
}
