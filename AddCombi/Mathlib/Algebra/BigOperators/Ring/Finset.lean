module

public import AddCombi.Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped Indicator

public section

namespace Finset
variable {α R : Type*} [Fintype α] [Semiring R]

@[simp] lemma sum_indicator_one (s : Finset α) : ∑ x, 𝟭_[(s : Set α), R] x = #s := by
  classical simp [Set.indicator_apply]

end Finset
