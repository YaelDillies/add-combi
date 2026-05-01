module

public import APAP.Prereqs.LpNorm.Compact
public import Mathlib.Analysis.RCLike.Inner

import APAP.Prereqs.Inner.Hoelder.Discrete
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity

/-! # Inner product -/

public section

open Finset hiding card
open Fintype (card)
open Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ENNReal NNReal NNRat

variable {ι κ 𝕜 : Type*} [Fintype ι]

namespace RCLike
variable [RCLike 𝕜] {mι : MeasurableSpace ι} [DiscreteMeasurableSpace ι] {f : ι → 𝕜}

@[simp] lemma wInner_cWeight_self (f : ι → 𝕜) :
    ⟪f, f⟫ₙ_[𝕜] = ((‖f‖ₙ_[2] : ℝ) : 𝕜) ^ 2 := by
  simp_rw [← algebraMap.coe_pow]
  simp [cL2Norm_sq_eq_expect_norm, wInner_cWeight_eq_expect]

set_option backward.isDefEq.respectTransparency false in
lemma cL1Norm_mul (f g : ι → 𝕜) : ‖f * g‖ₙ_[1] = ⟪fun i ↦ ‖f i‖, fun i ↦ ‖g i‖⟫ₙ_[ℝ] := by
  simp [wInner_cWeight_eq_expect, cL1Norm_eq_expect_norm, mul_comm]

set_option backward.isDefEq.respectTransparency false in
/-- **Cauchy-Schwarz inequality** -/
lemma wInner_cWeight_le_cL2Norm_mul_cL2Norm (f g : ι → ℝ) : ⟪f, g⟫ₙ_[ℝ] ≤ ‖f‖ₙ_[2] * ‖g‖ₙ_[2] := by
  simp only [wInner_cWeight_eq_smul_wInner_one, ← NNRat.cast_smul_eq_nnqsmul ℝ≥0, NNRat.cast_inv,
    NNRat.cast_natCast, NNReal.smul_def, NNReal.coe_inv, NNReal.coe_natCast, smul_eq_mul,
    cL2Norm_eq_expect_norm, expect, card_univ, norm_eq_abs, sq_abs]
  rw [mul_rpow, mul_rpow, mul_mul_mul_comm, ← sq, ← rpow_two, rpow_inv_rpow]
  any_goals positivity
  gcongr
  simpa [dL2Norm_eq_sum_norm] using wInner_one_le_dL2Norm_mul_dL2Norm f g

end RCLike

/-! ### Hölder inequality -/

namespace MeasureTheory
section Real
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] {p q : ℝ≥0}
  {f g : α → ℝ}

lemma cL1Norm_mul_of_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : ‖f * g‖ₙ_[1] = ⟪f, g⟫ₙ_[ℝ] := by
  convert cL1Norm_mul f g using 2 <;> ext a <;> refine (norm_of_nonneg ?_).symm; exacts [hf _, hg _]

/-- **Hölder's inequality**, binary case. -/
lemma wInner_cWeight_le_cLpNorm_mul_cLpNorm (p q : ℝ≥0∞) [p.HolderConjugate q] :
    ⟪f, g⟫ₙ_[ℝ] ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] := by
  sorry
  -- have hp := hpq.ne_zero
  -- have hq := hpq.symm.ne_zero
  -- norm_cast at hp hq
  -- rw [wInner_cWeight_eq_expect, expect_eq_sum_div_card, cLpNorm_eq_expect_norm hp,
  --   cLpNorm_eq_expect_norm hq, expect_eq_sum_div_card, expect_eq_sum_div_card,
  --   NNReal.div_rpow, NNReal.div_rpow, ← NNReal.coe_mul, div_mul_div_comm, ← NNReal.rpow_add',
  --   hpq.coe.inv_add_inv_conj, NNReal.rpow_one]
  -- swap
  -- · simp [hpq.coe.inv_add_inv_conj]
  -- push_cast
  -- gcongr
  -- rw [← dLpNorm_eq_sum_norm hp, ← dLpNorm_eq_sum_norm hq, ← wInner_one_eq_sum]
  -- exact wInner_one_le_dLpNorm_mul_dLpNorm hpq.coe_ennreal _ _

/-- **Hölder's inequality**, binary case. -/
lemma abs_wInner_cWeight_le_dLpNorm_mul_dLpNorm (p q : ℝ≥0∞) [p.HolderConjugate q] :
    |⟪f, g⟫ₙ_[ℝ]| ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] :=
  (abs_wInner_le fun _ ↦ by dsimp; positivity).trans <|
    (wInner_cWeight_le_cLpNorm_mul_cLpNorm p q).trans_eq <| by simp [cLpNorm_abs .of_discrete]

end Real

section Hoelder
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] [RCLike 𝕜]
  {p q r : ℝ≥0∞} {f g : α → 𝕜}

set_option backward.isDefEq.respectTransparency false in
lemma norm_wInner_cWeight_le (f g : α → 𝕜) :
    ‖⟪f, g⟫ₙ_[𝕜]‖₊ ≤ ⟪fun a ↦ ‖f a‖, fun a ↦ ‖g a‖⟫ₙ_[ℝ] := by
  simpa [wInner_cWeight_eq_expect, norm_mul, mul_comm]
    using norm_expect_le (K := ℝ) (f := fun i ↦ conj (f i) * g i)

/-- **Hölder's inequality**, binary case. -/
lemma norm_wInner_cWeight_le_dLpNorm_mul_dLpNorm (p q : ℝ≥0∞) [p.HolderConjugate q] :
    ‖⟪f, g⟫ₙ_[𝕜]‖₊ ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] :=
  calc
    _ ≤ ⟪fun a ↦ ‖f a‖, fun a ↦ ‖g a‖⟫ₙ_[ℝ] := norm_wInner_cWeight_le _ _
    _ ≤ ‖fun a ↦ ‖f a‖‖ₙ_[p] * ‖fun a ↦ ‖g a‖‖ₙ_[q] := wInner_cWeight_le_cLpNorm_mul_cLpNorm _ _
    _ = ‖f‖ₙ_[p] * ‖g‖ₙ_[q] := by simp_rw [cLpNorm_norm .of_discrete]

omit [Fintype α]

variable [Finite α]

set_option backward.isDefEq.respectTransparency false in
/-- **Hölder's inequality**, binary case. -/
lemma cLpNorm_mul_le (p q : ℝ≥0∞) (hr₀ : r ≠ 0) [hpqr : ENNReal.HolderTriple p q r] :
    ‖f * g‖ₙ_[r] ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] := by
  cases nonempty_fintype α
  obtain rfl | p := p
  · sorry
  obtain rfl | q := q
  · sorry
  obtain rfl | r := r
  · sorry
  -- The following two come from `HolderTriple p q r`
  have hp₀ : p ≠ 0 := sorry
  have hq₀ : q ≠ 0 := sorry
  simp only [ENNReal.some_eq_coe] at *
  norm_cast at hr₀
  have : (‖(f * g) ·‖ ^ (r : ℝ)) = (‖f ·‖ ^ (r : ℝ)) * (‖g ·‖ ^ (r : ℝ)) := by ext; simp [mul_rpow]
  rw [cLpNorm_eq_expect_norm, rpow_inv_le_iff_of_pos, this, mul_rpow, cLpNorm_rpow', cLpNorm_rpow',
    expect, smul_sum]
  any_goals positivity
  have := hpqr.holderConjugate_div_div _ _ _ (mod_cast hr₀) ENNReal.coe_ne_top
  convert wInner_cWeight_le_cLpNorm_mul_cLpNorm (α := α) (p / r) (q / r) using 1
  simp [wInner, cWeight, NNRat.smul_def, mul_comm]

/-- **Hölder's inequality**, binary case. -/
lemma cL1Norm_mul_le (p q : ℝ≥0∞) [hpq : ENNReal.HolderConjugate p q] :
    ‖f * g‖ₙ_[1] ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] := cLpNorm_mul_le _ _ one_ne_zero

/-- **Hölder's inequality**, finitary case. -/
lemma cLpNorm_prod_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {p : ι → ℝ≥0} (hp : ∀ i, p i ≠ 0)
    (q : ℝ≥0) (hpq : ∑ i ∈ s, ((p i)⁻¹ : ℝ≥0∞) = (q : ℝ≥0∞)⁻¹) (f : ι → α → 𝕜) :
    ‖∏ i ∈ s, f i‖ₙ_[q] ≤ ∏ i ∈ s, ‖f i‖ₙ_[p i] := by
  induction hs using Finset.Nonempty.cons_induction generalizing q with
  | singleton => simp_all
  | cons i s hi hs ih =>
  simp_rw [prod_cons]
  rw [sum_cons, ← inv_inv (∑ _ ∈ _, _)] at hpq
  have : ENNReal.HolderTriple (p i) ↑(∑ i ∈ s, (p i)⁻¹)⁻¹ q := ⟨sorry⟩
  grw [cLpNorm_mul_le (p i) ↑(∑ i ∈ s, (p i)⁻¹)⁻¹ , ih]
  · rw [← ENNReal.coe_inv, inv_inv]
    · push_cast
      congr! with i
      exact (ENNReal.coe_inv <| hp _).symm
    · simpa [hp]
  · norm_cast
    rintro rfl
    simp [hp] at hpq

end Hoelder
end MeasureTheory
