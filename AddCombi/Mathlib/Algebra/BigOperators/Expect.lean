module

public import AddCombi.Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.BigOperators.Expect

open scoped BigOperators Indicator

public section

namespace Finset
variable {α R K : Type*} [Fintype α] [Semiring R] [Semifield K] [CharZero K]

@[simp] lemma expect_indicator_one (s : Finset α) : 𝔼 x, 𝟭_[(s : Set α), K] x = s.dens := by
  classical obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [Set.indicator_apply, *]

end Finset
