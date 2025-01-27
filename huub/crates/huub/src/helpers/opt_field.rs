//! Compile time optional field implementation.

use std::hash::{Hash, Hasher};

#[derive(Debug)]
/// Compile time optional field.
///
/// This is used to represent fields that may or may not be present in a struct,
/// based on a compile time constant.
///
/// Note that `B` is a `usize` constant because of implementation limitations in
/// Rust. It should, however, be a `bool` and only the values `0` and `1` should
/// be used.
pub(crate) struct OptField<const B: usize, T> {
	/// Content of the field, if any.
	value: [T; B],
}

impl<T> OptField<1, T> {
	/// Creates a new `OptField` with the given value.
	pub(crate) fn new(value: T) -> Self {
		Self { value: [value] }
	}
}

impl<const B: usize, T> OptField<B, T> {
	#[inline]
	/// Return the value of the `OptField`, if it exists.
	pub(crate) fn get(&self) -> Option<&T> {
		self.value.first()
	}
}

impl<const B: usize, T: Clone> Clone for OptField<B, T> {
	fn clone(&self) -> Self {
		Self {
			value: self.value.clone(),
		}
	}
}

impl<T> Default for OptField<0, T> {
	fn default() -> Self {
		Self { value: [] }
	}
}

impl<T: Default> Default for OptField<1, T> {
	fn default() -> Self {
		Self {
			value: [T::default()],
		}
	}
}

impl<const B: usize, T: Eq> Eq for OptField<B, T> {}

impl<const B: usize, T: Hash> Hash for OptField<B, T> {
	fn hash<H: Hasher>(&self, state: &mut H) {
		self.value.iter().for_each(|v| v.hash(state));
	}
}

impl<const B: usize, T: PartialEq> PartialEq for OptField<B, T> {
	fn eq(&self, other: &Self) -> bool {
		self.value == other.value
	}
}
