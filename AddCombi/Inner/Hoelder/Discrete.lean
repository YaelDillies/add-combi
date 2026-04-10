module

public import APAP.Prereqs.LpNorm.Discrete.Defs
public import Mathlib.Analysis.RCLike.Inner

import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Inner product -/

public section

open Finset Function MeasureTheory RCLike Real
open scoped ComplexConjugate ENNReal NNReal NNRat

variable {ι 𝕜 S : Type*} [Fintype ι]

namespace RCLike
variable [RCLike 𝕜] {mι : MeasurableSpace ι} [DiscreteMeasurableSpace ι] {f : ι → 𝕜}

@[simp] lemma wInner_one_self {_ : MeasurableSpace ι} [DiscreteMeasurableSpace ι] (f : ι → 𝕜) :
    ⟪f, f⟫_[𝕜] = ((‖f‖_[2] : ℝ) : 𝕜) ^ 2 := by
  simp_rw [← algebraMap.coe_pow]
  simp [dL2Norm_sq_eq_sum_norm, wInner_one_eq_sum]

set_option backward.isDefEq.respectTransparency false in
lemma dL1Norm_mul (f g : ι → 𝕜) : ‖f * g‖_[1] = ⟪fun i ↦ ‖f i‖, fun i ↦ ‖g i‖⟫_[ℝ] := by
  simp [wInner_one_eq_sum, dL1Norm_eq_sum_norm, mul_comm]

set_option backward.isDefEq.respectTransparency false in
/-- **Cauchy-Schwarz inequality** -/
lemma wInner_one_le_dL2Norm_mul_dL2Norm (f g : ι → ℝ) : ⟪f, g⟫_[ℝ] ≤ ‖f‖_[2] * ‖g‖_[2] := by
  simpa [dL2Norm_eq_sum_norm, PiLp.norm_eq_of_L2, sqrt_eq_rpow, wInner_one_eq_inner]
    using real_inner_le_norm ((WithLp.equiv 2 _).symm f) _

end RCLike

/-! ### Hölder inequality -/

namespace MeasureTheory
section Real
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] {p q : ℝ≥0∞}
  {f g : α → ℝ}

lemma dL1Norm_mul_of_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : ‖f * g‖_[1] = ⟪f, g⟫_[ℝ] := by
  convert dL1Norm_mul f g using 2 <;> ext a <;> refine (norm_of_nonneg ?_).symm; exacts [hf _, hg _]

/-- **Hölder's inequality**, binary case. -/
lemma wInner_one_le_dLpNorm_mul_dLpNorm (p q : ℝ≥0∞) [p.HolderConjugate q] :
    ⟪f, g⟫_[ℝ] ≤ ‖f‖_[p] * ‖g‖_[q] := by
  sorry
  -- simpa [wInner_one_eq_sum, dLpNorm_eq_sum_nnnorm, *] using inner_le_Lp_mul_Lq _ f g _

/-- **Hölder's inequality**, binary case. -/
lemma abs_wInner_one_le_dLpNorm_mul_dLpNorm [p.HolderConjugate q] (f g : α → ℝ) :
    |⟪f, g⟫_[ℝ]| ≤ ‖f‖_[p] * ‖g‖_[q] :=
  (abs_wInner_le zero_le_one).trans <| (wInner_one_le_dLpNorm_mul_dLpNorm p q).trans_eq <| by
    simp_rw [dLpNorm_abs .of_discrete]

end Real

section Hoelder
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] [RCLike 𝕜]
  {p q r : ℝ≥0∞} {f g : α → 𝕜}

set_option backward.isDefEq.respectTransparency false in
lemma norm_wInner_one_le (f g : α → 𝕜) : ‖⟪f, g⟫_[𝕜]‖₊ ≤ ⟪fun a ↦ ‖f a‖, fun a ↦ ‖g a‖⟫_[ℝ] :=
  (norm_sum_le _ _).trans <| by simp [wInner_one_eq_sum]

/-- **Hölder's inequality**, binary case. -/
lemma nnnorm_wInner_one_le_dLpNorm_mul_dLpNorm (p q : ℝ≥0∞) [p.HolderConjugate q] :
    ‖⟪f, g⟫_[𝕜]‖₊ ≤ ‖f‖_[p] * ‖g‖_[q] :=
  calc
    _ ≤ ⟪fun a ↦ ‖f a‖, fun a ↦ ‖g a‖⟫_[ℝ] := norm_wInner_one_le _ _
    _ ≤ ‖fun a ↦ ‖f a‖‖_[p] * ‖fun a ↦ ‖g a‖‖_[q] := wInner_one_le_dLpNorm_mul_dLpNorm _ _
    _ = ‖f‖_[p] * ‖g‖_[q] := by simp_rw [dLpNorm_norm .of_discrete]

omit [Fintype α]
variable [Finite α]

/-- **Hölder's inequality**, binary case. -/
lemma dLpNorm_mul_le (p q : ℝ≥0∞) (hr₀ : r ≠ 0) [hpqr : ENNReal.HolderTriple p q r] :
    ‖f * g‖_[r] ≤ ‖f‖_[p] * ‖g‖_[q] := by
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
  rw [dLpNorm_eq_dL1Norm_rpow, rpow_inv_le_iff_of_pos, this]
  any_goals positivity
  rw [dL1Norm_mul_of_nonneg, mul_rpow, dLpNorm_rpow', dLpNorm_rpow']
  any_goals intro a; dsimp
  any_goals positivity
  any_goals simp
  have := hpqr.holderConjugate_div_div _ _ _ (mod_cast hr₀) ENNReal.coe_ne_top
  exact wInner_one_le_dLpNorm_mul_dLpNorm _ _

/-- **Hölder's inequality**, binary case. -/
lemma dL1Norm_mul_le (p q : ℝ≥0∞) [hpq : ENNReal.HolderConjugate p q] :
    ‖f * g‖_[1] ≤ ‖f‖_[p] * ‖g‖_[q] := dLpNorm_mul_le _ _ one_ne_zero

/-- **Hölder's inequality**, finitary case. -/
lemma dLpNorm_prod_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {p : ι → ℝ≥0} (hp : ∀ i, p i ≠ 0)
    (q : ℝ≥0) (hpq : ∑ i ∈ s, ((p i)⁻¹ : ℝ≥0∞) = (q : ℝ≥0∞)⁻¹) (f : ι → α → 𝕜) :
    ‖∏ i ∈ s, f i‖_[q] ≤ ∏ i ∈ s, ‖f i‖_[p i] := by
  induction s using Finset.cons_induction generalizing q with
  | empty => cases not_nonempty_empty hs
  | cons i s hi ih =>
    obtain rfl | hs := s.eq_empty_or_nonempty
    · simp only [sum_cons, sum_empty, add_zero, inv_inj] at hpq
      simp [← hpq]
    simp_rw [prod_cons]
    rw [sum_cons, ← inv_inv (∑ _ ∈ _, _)] at hpq
    have : ENNReal.HolderTriple (p i) ↑(∑ i ∈ s, (p i)⁻¹)⁻¹ q := ⟨sorry⟩
    grw [dLpNorm_mul_le (p i) ↑(∑ i ∈ s, (p i)⁻¹)⁻¹, ih hs]
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
