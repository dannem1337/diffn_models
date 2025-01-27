//! Propagation methods for the `table_int` constraint, which constraints a
//! sequence of integer decision variable to be assigned to a set of possible
//! sequences of integer values.

use itertools::Itertools;
use pindakaas::{solver::propagation::PropagatingSolver, VarRange};

use crate::{
	actions::InspectionActions,
	model::{int::IntView, reformulate::VariableMap},
	solver::engine::Engine,
	BoolView, IntVal, LitMeaning, ReformulationError, Solver,
};

/// Encode a [`Constraint::TableInt`] constraint into clauses in the solver such
/// that using clausal propagation will enforce global arc consistency.
pub(crate) fn encode_table_int_gac<Oracle: PropagatingSolver<Engine>>(
	slv: &mut Solver<Oracle>,
	map: &mut VariableMap,
	vars: &[IntView],
	vals: &[Vec<IntVal>],
) -> Result<(), ReformulationError> {
	assert!(vars.len() >= 2);

	let selector = if vars.len() != 2 {
		slv.oracle.new_var_range(vals.len())
	} else {
		VarRange::empty()
	};
	let vars = vars.iter().map(|iv| map.get_int(slv, iv)).collect_vec();

	// Create clauses that say foreach tuple i, if `selector[i]` is true, then the
	// variable `j` equals `vals[i][j]`.
	if vars.len() != 2 {
		for (i, tup) in vals.iter().enumerate() {
			assert!(tup.len() == vars.len());
			let lit: BoolView = selector.index(i).into();
			for (j, var) in vars.iter().enumerate() {
				let clause = [!lit, slv.get_int_lit(*var, LitMeaning::Eq(tup[j]))];
				slv.add_clause(clause)?;
			}
		}
	}

	// Create clauses that map from the value taken by the variables back to the
	// possible selectors that can be active.
	for (j, var) in vars.iter().enumerate() {
		let (lb, ub) = slv.get_int_bounds(*var);
		let mut support_clauses: Vec<Vec<BoolView>> = vec![Vec::new(); (ub - lb + 1) as usize];
		for (i, tup) in vals.iter().enumerate() {
			let k = tup[j] - lb;
			if !(0..support_clauses.len() as IntVal).contains(&k) {
				// Value is not in the domain of the variable, so this tuple should not
				// be considered.
				continue;
			}
			// Add tuple i to be in support of value `k`.
			if vars.len() == 2 {
				// Special case where we can use the values of the other variables as
				// the selection variables directly.
				support_clauses[k as usize]
					.push(slv.get_int_lit(vars[1 - j], LitMeaning::Eq(tup[1 - j])));
			} else {
				support_clauses[k as usize].push(selector.index(i).into());
			}
		}
		for (i, mut clause) in support_clauses.into_iter().enumerate() {
			if slv.check_int_in_domain(*var, lb + i as IntVal) {
				clause.push(slv.get_int_lit(vars[j], LitMeaning::NotEq(lb + i as IntVal)));
				slv.add_clause(clause)?;
			}
		}
	}

	Ok(())
}

#[cfg(test)]
mod tests {
	use expect_test::expect;
	use itertools::Itertools;

	use crate::{model::ModelView, Constraint, InitConfig, Model};

	#[test]
	fn test_binary_table_sat() {
		let mut prb = Model::default();
		let vars = prb.new_int_vars(3, (1..=5).into());
		let table = vec![
			vec![1, 3],
			vec![1, 4],
			vec![2, 4],
			vec![2, 5],
			vec![3, 1],
			vec![3, 5],
			vec![4, 1],
			vec![4, 2],
			vec![5, 2],
			vec![5, 3],
		];
		prb += Constraint::TableInt(vec![vars[0].into(), vars[1].into()], table.clone());
		prb += Constraint::TableInt(vec![vars[1].into(), vars[2].into()], table.clone());

		let (mut slv, map) = prb.to_solver(&InitConfig::default()).unwrap();
		let vars = vars
			.into_iter()
			.map(|x| map.get(&mut slv, &ModelView::Int(x.into())))
			.collect_vec();
		slv.expect_solutions(
			&vars,
			expect![[r#"
    1, 3, 1
    1, 3, 5
    1, 4, 1
    1, 4, 2
    2, 4, 1
    2, 4, 2
    2, 5, 2
    2, 5, 3
    3, 1, 3
    3, 1, 4
    3, 5, 2
    3, 5, 3
    4, 1, 3
    4, 1, 4
    4, 2, 4
    4, 2, 5
    5, 2, 4
    5, 2, 5
    5, 3, 1
    5, 3, 5"#]],
		);
	}

	#[test]
	fn test_tertiary_table_sat() {
		let mut prb = Model::default();
		let vars = prb.new_int_vars(5, (1..=5).into());
		let table = vec![
			vec![1, 3, 1],
			vec![1, 3, 5],
			vec![2, 4, 2],
			vec![3, 1, 3],
			vec![3, 5, 3],
			vec![4, 2, 4],
			vec![5, 3, 1],
			vec![5, 3, 5],
		];
		prb += Constraint::TableInt(
			vars[0..3].iter().cloned().map_into().collect_vec(),
			table.clone(),
		);
		prb += Constraint::TableInt(
			vars[2..5].iter().cloned().map_into().collect_vec(),
			table.clone(),
		);

		let (mut slv, map) = prb.to_solver(&InitConfig::default()).unwrap();
		let vars = vars
			.into_iter()
			.map(|x| map.get(&mut slv, &ModelView::Int(x.into())))
			.collect_vec();
		slv.expect_solutions(
			&vars,
			expect![[r#"
    1, 3, 1, 3, 1
    1, 3, 1, 3, 5
    1, 3, 5, 3, 1
    1, 3, 5, 3, 5
    2, 4, 2, 4, 2
    3, 1, 3, 1, 3
    3, 1, 3, 5, 3
    3, 5, 3, 1, 3
    3, 5, 3, 5, 3
    4, 2, 4, 2, 4
    5, 3, 1, 3, 1
    5, 3, 1, 3, 5
    5, 3, 5, 3, 1
    5, 3, 5, 3, 5"#]],
		);
	}
}
