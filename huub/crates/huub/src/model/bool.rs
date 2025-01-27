//! Representation and manipulation of Boolean decision variable and expressions
//! in [`Model`].

use std::{iter::once, ops::Not};

use pindakaas::{
	propositional_logic::{Formula, TseitinEncoder},
	solver::propagation::PropagatingSolver,
	Lit as RawLit,
};

use crate::{
	model::{
		int,
		reformulate::{ReformulationError, VariableMap},
	},
	solver::{
		engine::Engine,
		view::{self, BoolViewInner},
	},
	IntVal, Solver,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// A propositional logic formula that can be used as part of a [`Constraint`]
/// in a [`Model`].
pub enum BoolExpr {
	/// Direct Boolean view
	View(BoolView),
	/// Logical negation of a Boolean expression.
	Not(Box<BoolExpr>),
	/// Disjunction of a list of Boolean expressions.
	Or(Vec<BoolExpr>),
	/// Conjunction of a list of Boolean expressions.
	And(Vec<BoolExpr>),
	/// Logical implication of the first Boolean expression to the second.
	Implies(Box<BoolExpr>, Box<BoolExpr>),
	/// Logical equivalence of a list of Boolean expressions.
	Equiv(Vec<BoolExpr>),
	/// Exclusive disjunction of a list of Boolean expressions.
	Xor(Vec<BoolExpr>),
	/// If-then-else expression: if the condition holds, then the `then`
	/// expression must also hold, otherwise the `els` expression must hold.
	IfThenElse {
		/// Condition expression, choosing between the `then` and `els`.
		cond: Box<BoolExpr>,
		/// Expression that must hold if the condition holds.
		then: Box<BoolExpr>,
		/// Expression that must hold if the condition does not hold.
		els: Box<BoolExpr>,
	},
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[allow(
	variant_size_differences,
	reason = "`bool` is smaller than all other variants"
)]
/// A Boolean expression that is represented using a literal or a constaint in
/// the oracle SAT solver.
pub enum BoolView {
	/// A Boolean decision variable or its negation.
	Lit(RawLit),
	/// A constant Boolean value.
	Const(bool),
	/// Wether an integer is equal to a constant.
	IntEq(Box<int::IntView>, IntVal),
	/// Wether an integer is greater than a constant.
	IntGreater(Box<int::IntView>, IntVal),
	/// Wether an integer is greater or equal to a constant.
	IntGreaterEq(Box<int::IntView>, IntVal),
	/// Wether an integer is less than a constant.
	IntLess(Box<int::IntView>, IntVal),
	/// Wether an integer is less or equal to a constant.
	IntLessEq(Box<int::IntView>, IntVal),
	/// Wether an integer is not equal to a constant.
	IntNotEq(Box<int::IntView>, IntVal),
}

impl BoolExpr {
	/// Add clauses to the solver to enforce the Boolean expression.
	pub(crate) fn constrain<Oracle: PropagatingSolver<Engine>>(
		&self,
		slv: &mut Solver<Oracle>,
		map: &mut VariableMap,
	) -> Result<(), ReformulationError> {
		match self {
			BoolExpr::View(bv) => {
				let v = map.get_bool(slv, bv);
				slv.add_clause([v])
			}
			BoolExpr::Not(x) => {
				if let Some(y) = x.push_not_inward() {
					y.constrain(slv, map)
				} else {
					let r = x.to_arg(slv, map, None)?;
					slv.add_clause([!r])
				}
			}
			BoolExpr::Or(es) => {
				let mut lits = Vec::with_capacity(es.len());
				for e in es {
					match e.to_arg(slv, map, None)?.0 {
						BoolViewInner::Const(false) => {}
						BoolViewInner::Const(true) => return Ok(()),
						BoolViewInner::Lit(l) => lits.push(l),
					}
				}
				slv.oracle
					.add_clause(lits)
					.map_err(|_| ReformulationError::TrivialUnsatisfiable)
			}
			BoolExpr::And(es) => {
				for e in es {
					match e.to_arg(slv, map, None)?.0 {
						BoolViewInner::Const(false) => {
							return Err(ReformulationError::TrivialUnsatisfiable)
						}
						BoolViewInner::Const(true) => {}
						BoolViewInner::Lit(l) => slv
							.oracle
							.add_clause([l])
							.map_err(|_| ReformulationError::TrivialUnsatisfiable)?,
					}
				}
				Ok(())
			}
			BoolExpr::Implies(a, b) => {
				let a = match a.to_arg(slv, map, None)?.0 {
					BoolViewInner::Const(true) => {
						return b.constrain(slv, map);
					}
					BoolViewInner::Const(false) => {
						return Ok(());
					}
					BoolViewInner::Lit(l) => l,
				};

				// TODO: Conditional Compilation
				match b.to_arg(slv, map, None)?.0 {
					BoolViewInner::Const(true) => Ok(()),
					BoolViewInner::Const(false) => slv
						.oracle
						.add_clause([!a])
						.map_err(|_| ReformulationError::TrivialUnsatisfiable),
					BoolViewInner::Lit(b) => slv
						.oracle
						.add_clause([!a, b])
						.map_err(|_| ReformulationError::TrivialUnsatisfiable),
				}
			}
			BoolExpr::Equiv(es) => {
				// Try and find some constant or literal to start binding to
				let mut res = es.iter().find_map(|e| {
					if let BoolExpr::View(b) = e {
						Some(map.get_bool(slv, b))
					} else {
						None
					}
				});
				for e in es {
					match res {
						Some(view::BoolView(BoolViewInner::Const(false))) => {
							(!e).constrain(slv, map)?;
						}
						Some(view::BoolView(BoolViewInner::Const(true))) => {
							e.constrain(slv, map)?;
						}
						Some(view::BoolView(BoolViewInner::Lit(name))) => {
							res = Some(e.to_arg(slv, map, Some(name))?);
						}
						None => res = Some(e.to_arg(slv, map, None)?),
					}
				}
				Ok(())
			}
			BoolExpr::Xor(es) => {
				let mut lits = Vec::with_capacity(es.len());
				let mut count = 0;
				for e in es {
					match e.to_arg(slv, map, None)?.0 {
						BoolViewInner::Const(true) => count += 1,
						BoolViewInner::Const(false) => {}
						BoolViewInner::Lit(l) => lits.push(Formula::Atom(l)),
					}
				}
				let mut formula = Formula::Xor(lits);
				if count % 2 == 1 {
					formula = !formula;
				}
				slv.oracle
					.encode(&formula, &TseitinEncoder)
					.map_err(|_| ReformulationError::TrivialUnsatisfiable)
			}
			BoolExpr::IfThenElse { cond, then, els } => match cond.to_arg(slv, map, None)?.0 {
				BoolViewInner::Const(true) => then.constrain(slv, map),
				BoolViewInner::Const(false) => els.constrain(slv, map),
				BoolViewInner::Lit(_) => BoolExpr::And(vec![
					BoolExpr::Or(vec![!*cond.clone(), *then.clone()]),
					BoolExpr::Or(vec![*cond.clone(), *els.clone()]),
				])
				.constrain(slv, map),
			},
		}
	}

	/// Helper function that takes an expression that was contains in a
	/// [`BoolExpr::Not`] and return an equivalent expression that is equivalent
	/// to the negation of the original expression by pushing the negation
	/// inwards. If this is not possible, then `None` is returned.
	fn push_not_inward(&self) -> Option<BoolExpr> {
		Some(match self {
			BoolExpr::View(v) => BoolExpr::View(!v),
			BoolExpr::Not(e) => *e.clone(),
			BoolExpr::Or(es) => BoolExpr::And(es.iter().map(|e| !e).collect()),
			BoolExpr::And(es) => BoolExpr::Or(es.iter().map(|e| !e).collect()),
			BoolExpr::Implies(a, b) => BoolExpr::And(vec![*a.clone(), !*b.clone()]),
			BoolExpr::IfThenElse { cond, then, els } => BoolExpr::IfThenElse {
				cond: cond.clone(),
				then: Box::new(!*then.clone()),
				els: Box::new(!*els.clone()),
			},
			BoolExpr::Xor(es) => {
				BoolExpr::Xor(once(true.into()).chain(es.iter().cloned()).collect())
			}
			BoolExpr::Equiv(es) => {
				if let [a, b] = es.as_slice() {
					BoolExpr::Xor(vec![a.clone(), b.clone()])
				} else {
					return None;
				}
			}
		})
	}

	/// Reifies the Boolean expression into a Boolean view (which will be a
	/// literal or constant in the oracle solver).
	pub(crate) fn to_arg<Oracle: PropagatingSolver<Engine>>(
		&self,
		slv: &mut Solver<Oracle>,
		map: &mut VariableMap,
		name: Option<RawLit>,
	) -> Result<view::BoolView, ReformulationError> {
		let bind_lit = |oracle: &mut Oracle, lit| {
			Ok(view::BoolView(BoolViewInner::Lit(
				if let Some(name) = name {
					oracle
						.encode(
							&Formula::Equiv(vec![Formula::Atom(name), Formula::Atom(lit)]),
							&TseitinEncoder,
						)
						.map_err(|_| ReformulationError::TrivialUnsatisfiable)?;
					name
				} else {
					lit
				},
			)))
		};
		let bind_const = |oracle: &mut Oracle, val| {
			if let Some(name) = name {
				oracle
					.add_clause([if val { name } else { !name }])
					.map_err(|_| ReformulationError::TrivialUnsatisfiable)?;
			}
			Ok(view::BoolView(BoolViewInner::Const(val)))
		};
		let bind_view = |oracle: &mut Oracle, view: view::BoolView| match view.0 {
			BoolViewInner::Lit(l) => bind_lit(oracle, l),
			BoolViewInner::Const(c) => bind_const(oracle, c),
		};
		match self {
			BoolExpr::View(v) => {
				let view = map.get_bool(slv, v);
				bind_view(&mut slv.oracle, view)
			}
			BoolExpr::Not(x) => {
				if let Some(y) = x.push_not_inward() {
					y.to_arg(slv, map, name)
				} else {
					let r = x.to_arg(slv, map, name.map(|e| !e))?;
					Ok(!r)
				}
			}
			BoolExpr::Or(es) => {
				let mut lits = Vec::with_capacity(es.len());
				for e in es {
					match e.to_arg(slv, map, None)?.0 {
						BoolViewInner::Const(false) => {}
						BoolViewInner::Const(true) => return bind_const(&mut slv.oracle, true),
						BoolViewInner::Lit(l) => lits.push(Formula::Atom(l)),
					}
				}
				let r = name.unwrap_or_else(|| slv.oracle.new_lit());
				slv.oracle
					.encode(
						&Formula::Equiv(vec![Formula::Atom(r), Formula::Or(lits)]),
						&TseitinEncoder,
					)
					.unwrap();
				Ok(view::BoolView(BoolViewInner::Lit(r)))
			}
			BoolExpr::And(es) => {
				let mut lits = Vec::with_capacity(es.len());
				for e in es {
					match e.to_arg(slv, map, None)?.0 {
						BoolViewInner::Const(true) => {}
						BoolViewInner::Const(false) => return bind_const(&mut slv.oracle, false),
						BoolViewInner::Lit(l) => lits.push(Formula::Atom(l)),
					}
				}
				let name = name.unwrap_or_else(|| slv.oracle.new_lit());
				slv.oracle
					.encode(
						&Formula::Equiv(vec![Formula::Atom(name), Formula::And(lits)]),
						&TseitinEncoder,
					)
					.unwrap();
				Ok(view::BoolView(BoolViewInner::Lit(name)))
			}
			BoolExpr::Implies(a, b) => {
				let a = match a.to_arg(slv, map, None)?.0 {
					BoolViewInner::Const(true) => return b.to_arg(slv, map, name),
					BoolViewInner::Const(false) => return bind_const(&mut slv.oracle, true),
					BoolViewInner::Lit(l) => l,
				};

				// TODO: Conditional encoding
				match b.to_arg(slv, map, None)?.0 {
					BoolViewInner::Const(true) => bind_const(&mut slv.oracle, true),
					BoolViewInner::Const(false) => bind_lit(&mut slv.oracle, !a),
					BoolViewInner::Lit(b) => {
						let name = name.unwrap_or_else(|| slv.oracle.new_lit());
						slv.oracle
							.encode(
								&Formula::Equiv(vec![
									Formula::Atom(name),
									Formula::Implies(
										Box::new(Formula::Atom(a)),
										Box::new(Formula::Atom(b)),
									),
								]),
								&TseitinEncoder,
							)
							.unwrap();
						Ok(view::BoolView(BoolViewInner::Lit(name)))
					}
				}
			}
			BoolExpr::Equiv(es) => {
				let mut lits = Vec::with_capacity(es.len());
				let mut res = None;
				for e in es {
					match e.to_arg(slv, map, None)?.0 {
						BoolViewInner::Const(b) => match res {
							None => res = Some(b),
							Some(b2) if b != b2 => {
								return bind_const(&mut slv.oracle, false);
							}
							Some(_) => {}
						},
						BoolViewInner::Lit(l) => lits.push(Formula::Atom(l)),
					}
				}
				let name = name.unwrap_or_else(|| slv.oracle.new_lit());
				let f = match res {
					Some(b) => {
						Formula::And(lits.into_iter().map(|e| if b { e } else { !e }).collect())
					}
					None => Formula::Equiv(lits),
				};
				slv.oracle
					.encode(
						&Formula::Equiv(vec![Formula::Atom(name), f]),
						&TseitinEncoder,
					)
					.unwrap();
				Ok(view::BoolView(BoolViewInner::Lit(name)))
			}
			BoolExpr::Xor(es) => {
				let mut lits = Vec::with_capacity(es.len());
				let mut count = 0;
				for e in es {
					match e.to_arg(slv, map, None)?.0 {
						BoolViewInner::Const(true) => count += 1,
						BoolViewInner::Const(false) => {}
						BoolViewInner::Lit(l) => lits.push(Formula::Atom(l)),
					}
				}
				let name = name.unwrap_or_else(|| slv.oracle.new_lit());
				let mut formula = Formula::Xor(lits);
				if count % 2 == 1 {
					formula = !formula;
				}
				slv.oracle
					.encode(
						&Formula::Equiv(vec![Formula::Atom(name), formula]),
						&TseitinEncoder,
					)
					.unwrap();
				Ok(view::BoolView(BoolViewInner::Lit(name)))
			}
			BoolExpr::IfThenElse { cond, then, els } => {
				match cond.to_arg(slv, map, None)?.0 {
					BoolViewInner::Const(true) => then.to_arg(slv, map, name),
					BoolViewInner::Const(false) => then.to_arg(slv, map, name),
					// TODO: Conditional encoding
					BoolViewInner::Lit(_) => BoolExpr::And(vec![
						BoolExpr::Or(vec![!*cond.clone(), *then.clone()]),
						BoolExpr::Or(vec![*cond.clone(), *els.clone()]),
					])
					.to_arg(slv, map, name),
				}
			}
		}
	}
}
impl From<&BoolView> for BoolExpr {
	fn from(v: &BoolView) -> Self {
		Self::View(v.clone())
	}
}
impl From<BoolView> for BoolExpr {
	fn from(v: BoolView) -> Self {
		Self::View(v)
	}
}

impl From<bool> for BoolExpr {
	fn from(v: bool) -> Self {
		Self::View(v.into())
	}
}

impl Not for BoolExpr {
	type Output = BoolExpr;

	fn not(self) -> Self::Output {
		match self {
			BoolExpr::View(v) => BoolExpr::View(!v),
			BoolExpr::Not(e) => *e,
			_ => BoolExpr::Not(Box::new(self)),
		}
	}
}

impl Not for &BoolExpr {
	type Output = BoolExpr;

	fn not(self) -> Self::Output {
		!self.clone()
	}
}

impl From<bool> for BoolView {
	fn from(v: bool) -> Self {
		BoolView::Const(v)
	}
}

impl Not for BoolView {
	type Output = BoolView;

	fn not(self) -> Self::Output {
		match self {
			BoolView::Lit(l) => BoolView::Lit(!l),
			BoolView::Const(b) => BoolView::Const(!b),
			BoolView::IntEq(v, i) => BoolView::IntNotEq(v, i),
			BoolView::IntGreater(v, i) => BoolView::IntLessEq(v, i),
			BoolView::IntGreaterEq(v, i) => BoolView::IntLess(v, i),
			BoolView::IntLess(v, i) => BoolView::IntGreaterEq(v, i),
			BoolView::IntLessEq(v, i) => BoolView::IntGreater(v, i),
			BoolView::IntNotEq(v, i) => BoolView::IntEq(v, i),
		}
	}
}

impl Not for &BoolView {
	type Output = BoolView;

	fn not(self) -> Self::Output {
		!(self.clone())
	}
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use itertools::Itertools;

	use crate::{model::bool::BoolView, BoolExpr, InitConfig, Model, Solver};

	#[test]
	fn test_bool_and() {
		// Simple Satisfiable test case
		let mut m = Model::default();
		let b = m.new_bool_vars(3);

		m += BoolExpr::And(b.iter().cloned().map_into().collect());
		let (mut slv, map): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		let vars: Vec<_> = b
			.into_iter()
			.map(|x| map.get(&mut slv, &x.into()))
			.collect();
		slv.expect_solutions(&vars, expect!["true, true, true"]);

		// Simple Unsatisfiable test case
		let mut m = Model::default();
		let b = m.new_bool_vars(3);

		m += BoolExpr::And(b.iter().cloned().map_into().collect());
		m += BoolExpr::from(!b[0].clone());
		let (mut slv, _): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		slv.assert_unsatisfiable();

		// Regression test case: empty and
		let mut m = Model::default();
		let b = m.new_bool_var();

		m += BoolExpr::Equiv(vec![
			b.clone().into(),
			BoolExpr::And(vec![true.into(), true.into(), true.into()]),
		]);
		let (mut slv, map): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		let vars = vec![map.get(&mut slv, &b.into())];
		slv.expect_solutions(&vars, expect!["true"]);
	}

	#[test]
	fn test_bool_and_reif() {
		// Simple Satisfiable test case
		let mut m = Model::default();
		let b = m.new_bool_vars(3);

		m += BoolExpr::Equiv(vec![
			b[0].clone().into(),
			BoolExpr::And(vec![b[1].clone().into(), b[2].clone().into()]),
		]);
		let (mut slv, map): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		let vars: Vec<_> = b
			.into_iter()
			.map(|x| map.get(&mut slv, &x.into()))
			.collect();
		slv.expect_solutions(
			&vars,
			expect![[r#"
		false, false, false
		false, false, true
		false, true, false
		true, true, true"#]],
		);
	}

	#[test]
	fn test_bool_clause_reif() {
		// Simple Satisfiable test case
		let mut m = Model::default();
		let b = m.new_bool_vars(3);

		m += BoolExpr::Equiv(vec![
			b[0].clone().into(),
			BoolExpr::Or(vec![b[1].clone().into(), b[2].clone().into()]),
		]);
		let (mut slv, map): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		let vars: Vec<_> = b
			.into_iter()
			.map(|x| map.get(&mut slv, &x.into()))
			.collect();
		slv.expect_solutions(
			&vars,
			expect![[r#"
		false, false, false
		true, false, true
		true, true, false
		true, true, true"#]],
		);
	}

	#[test]
	fn test_bool_eq_reif() {
		// Simple Satisfiable test case
		let mut m = Model::default();
		let b = m.new_bool_vars(3);

		m += BoolExpr::Equiv(vec![
			b[0].clone().into(),
			BoolExpr::Equiv(vec![b[1].clone().into(), b[2].clone().into()]),
		]);
		let (mut slv, map): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		let vars: Vec<_> = b
			.into_iter()
			.map(|x| map.get(&mut slv, &x.into()))
			.collect();
		slv.expect_solutions(
			&vars,
			expect![[r#"
		false, false, true
		false, true, false
		true, false, false
		true, true, true"#]],
		);
	}

	#[test]
	fn test_bool_not() {
		// Satisfiable test case that rewrites the expression
		let mut m = Model::default();
		let b = m.new_bool_vars(2);

		m += BoolExpr::Not(Box::new(BoolExpr::Xor(b.iter().map_into().collect())));
		let (mut slv, map): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		let vars: Vec<_> = b
			.into_iter()
			.map(|x| map.get(&mut slv, &x.into()))
			.collect();
		slv.expect_solutions(
			&vars,
			expect![[r#"
    false, false
    true, true"#]],
		);

		// Simple Satisfiable test case that reifies the test case
		let mut m = Model::default();
		let b = m.new_bool_vars(3);

		m += BoolExpr::Not(Box::new(BoolExpr::Equiv(b.iter().map_into().collect())));
		let (mut slv, map): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		let vars: Vec<_> = b
			.into_iter()
			.map(|x| map.get(&mut slv, &x.into()))
			.collect();
		slv.expect_solutions(
			&vars,
			expect![[r#"
    false, false, true
    false, true, false
    false, true, true
    true, false, false
    true, false, true
    true, true, false"#]],
		);
	}

	#[test]
	fn test_bool_or() {
		// Simple Satisfiable test case
		let mut m = Model::default();
		let b = m.new_bool_vars(3);

		m += BoolExpr::Or(b.iter().cloned().map_into().collect());
		let (mut slv, map): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		let vars: Vec<_> = b
			.into_iter()
			.map(|x| map.get(&mut slv, &x.into()))
			.collect();
		slv.expect_solutions(
			&vars,
			expect![[r#"
		false, false, true
		false, true, false
		false, true, true
		true, false, false
		true, false, true
		true, true, false
		true, true, true"#]],
		);

		// Simple Unsatisfiable test case
		let mut m = Model::default();
		let b = m.new_bool_vars(3);

		m += BoolExpr::Or(b.iter().cloned().map_into().collect());
		m += BoolExpr::And(b.iter().cloned().map(|l| (!l).into()).collect());
		let (mut slv, _): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		slv.assert_unsatisfiable();

		// Regression test case: empty or
		let mut m = Model::default();
		let b = m.new_bool_var();

		m += BoolExpr::Equiv(vec![
			b.clone().into(),
			BoolExpr::Or(vec![false.into(), false.into(), false.into()]),
		]);
		let (mut slv, map): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		let vars = vec![map.get(&mut slv, &b.into())];
		slv.expect_solutions(&vars, expect!["false"]);
	}

	#[test]
	fn test_bool_xor() {
		// Simple Satisfiable test case
		let mut m = Model::default();
		let b = m.new_bool_vars(3);

		m += BoolExpr::Xor(b.iter().cloned().map_into().collect());
		let (mut slv, map): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		let vars: Vec<_> = b
			.into_iter()
			.map(|x| map.get(&mut slv, &x.into()))
			.collect();
		slv.expect_solutions(
			&vars,
			expect![[r#"
				false, false, true
				false, true, false
				true, false, false
				true, true, true"#]],
		);

		// Regression test case
		let mut m = Model::default();
		let b = m.new_bool_vars(2);

		m += BoolExpr::Equiv(vec![
			BoolExpr::View(b[1].clone()),
			BoolExpr::Xor(vec![
				BoolExpr::View(BoolView::Const(true)),
				BoolExpr::View(b[0].clone()),
			]),
		]);
		let (mut slv, map): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		let vars: Vec<_> = b
			.into_iter()
			.map(|x| map.get(&mut slv, &x.into()))
			.collect();
		slv.expect_solutions(
			&vars,
			expect![[r#"
				false, true
				true, false"#]],
		);

		// Simple Unsatisfiable test case
		let mut m = Model::default();
		let b = m.new_bool_vars(2);

		m += BoolExpr::Xor(b.iter().cloned().map_into().collect());
		m += BoolExpr::from(!b[0].clone());
		m += BoolExpr::from(!b[1].clone());
		let (mut slv, _): (Solver, _) = m.to_solver(&InitConfig::default()).unwrap();
		slv.assert_unsatisfiable();
	}
}
