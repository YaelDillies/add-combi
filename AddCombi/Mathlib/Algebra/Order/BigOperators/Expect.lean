module

public import Mathlib.Algebra.Order.BigOperators.Expect

public section

variable {ι M R : Type*}

local notation a " /ℚ " q => (q : ℚ≥0)⁻¹ • a

open scoped BigOperators

namespace Finset
variable [AddCommMonoid M] [PartialOrder M] [IsOrderedCancelAddMonoid M] [Module ℚ≥0 M]
  [PosSMulStrictMono ℚ≥0 M] {s : Finset ι} {f g : ι → M}

lemma expect_pos' (h : ∀ i ∈ s, 0 ≤ f i) (hs : ∃ i ∈ s, 0 < f i) : 0 < 𝔼 i ∈ s, f i :=
  (expect_const_zero _).symm.trans_lt <| expect_lt_expect h hs

end Finset
