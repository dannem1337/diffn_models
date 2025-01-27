//! # Huub - A Modular and Maintainable Lazy Clause Generation Solver
//!
//! Huub is a Lazy Clause Generation (LCG) solver with a focus on modularity and
//! maintainability in addition to speed. LCG solvers are a class of solvers
//! that can be used to solve decision and optimization problems. They are
//! characterized by their ability to dynamically add new Boolean variables and
//! clauses to a Boolean Satisfiability (SAT) solver during the search process.
//! This allows the solver exploit SAT solver's ability to learn from failures
//! during the search process, without having to encode the full problem into
//! Boolean variables and clauses.

pub(crate) mod actions;
pub(crate) mod brancher;
pub(crate) mod helpers;
pub(crate) mod model;
pub(crate) mod propagator;
pub(crate) mod solver;
#[cfg(test)]
pub(crate) mod tests;

pub use helpers::linear_transform::LinearTransform;
pub use model::{
	bool::BoolExpr,
	constraint::Constraint,
	flatzinc::{FlatZincError, FlatZincStatistics},
	reformulate::{InitConfig, ReformulationError},
	Model,
};
pub use pindakaas::solver::SlvTermSignal;
use pindakaas::Lit as RawLit;
pub use solver::{
	engine::int_var::LitMeaning,
	value::{IntSetVal, IntVal, NonZeroIntVal, Valuation, Value},
	view::{BoolView, IntView, SolverView},
	Goal, SolveResult, Solver,
};

/// Type alias for a disjunction of literals (clause), used for internal type
/// documentation.
type Clause<L = RawLit> = Vec<L>;

/// Type alias for a conjunction of literals (clause), used for internal type
/// documentation.
type Conjunction<L = RawLit> = Vec<L>;
