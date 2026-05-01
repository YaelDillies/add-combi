module

public import APAP.Prereqs.Function.Indicator.Defs
public import Mathlib.Algebra.AddTorsor.Defs
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Group.Translate
public import Mathlib.Algebra.Star.Conjneg

import Mathlib.Algebra.Group.Action.Pointwise.Finset

@[expose] public section

open Finset Function
open Fintype (card)
open scoped BigOperators ComplexConjugate Pointwise translate mu

local notation a " /ℚ " q => (q : ℚ≥0)⁻¹ • a

/-! ### Indicator -/

variable {ι α β γ : Type*} [DecidableEq α]

section Semiring
variable [Semiring β] [Semiring γ] {s : Finset α}

variable (β)

lemma translate_indicator [AddCommGroup α] (a : α) (s : Finset α) : τ a (𝟭_[β] s) = 𝟭 (a +ᵥ s) := by
  ext; simp [indicator_apply, ← neg_vadd_mem_iff, sub_eq_neg_add]

end Semiring

section CommSemiring
variable [CommSemiring β] [StarRing β] [AddCommGroup α]

@[simp] lemma conjneg_indicator (s : Finset α) : conjneg (𝟭_[β] s) = 𝟭 (-s) := by ext; simp

end CommSemiring

section Semifield
variable [Fintype ι] [DecidableEq ι] [Semiring β] [Module ℚ≥0 β]

lemma expect_indicator (s : Finset ι) : 𝔼 x, 𝟭_[β] s x = #s /ℚ Fintype.card ι := by
  simp only [expect_univ, indicator]
  rw [← sum_filter, filter_mem_eq_inter, univ_inter, sum_const, Nat.smul_one_eq_cast]

end Semifield

/-! ### Normalised indicator -/

section DivisionSemiring
variable [DivisionSemiring β] [DivisionSemiring γ] {s : Finset α}

variable (β)

lemma translate_mu [AddCommGroup α] (a : α) (s : Finset α) : τ a (μ_[β] s) = μ (a +ᵥ s) := by
  ext; simp [mu_apply, ← neg_vadd_mem_iff, sub_eq_neg_add]

end DivisionSemiring

section Semifield
variable (β) [Semifield β] {s : Finset α}

lemma expect_mu [CharZero β] [Fintype α] (hs : s.Nonempty) : 𝔼 x, μ_[β] s x = (↑(card α))⁻¹ := by
  rw [expect, card_univ, sum_mu _ hs, NNRat.smul_one_eq_cast, NNRat.cast_inv, NNRat.cast_natCast]

variable [StarRing β]

@[simp] lemma conjneg_mu [AddCommGroup α] (s : Finset α) : conjneg (μ_[β] s) = μ (-s) := by
  ext; simp

end Semifield
