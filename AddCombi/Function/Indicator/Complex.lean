module

public import APAP.Prereqs.Function.Indicator.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Complex.Basic

import Mathlib.LinearAlgebra.Complex.Module

public section

open Finset Function
open Fintype (card)
open scoped ComplexConjugate Pointwise NNRat mu

/-! ### Indicator -/

variable {ι α β γ : Type*} [DecidableEq α]

section Semiring
variable [Semiring β] [Semiring γ] {s : Finset α}

variable (β)
variable {β}
variable [StarRing β]

lemma indicator_isSelfAdjoint (s : Finset α) : IsSelfAdjoint (𝟭_[β] s) :=
  Pi.isSelfAdjoint.2 fun g ↦ by rw [indicator]; split_ifs <;> simp

end Semiring

namespace NNReal
open scoped NNReal

@[simp, norm_cast] lemma coe_indicator (s : Finset α) (x : α) : ↑(𝟭_[ℝ≥0] s x) = 𝟭_[ℝ] s x :=
  map_indicator NNReal.toRealHom _ _

@[simp] lemma coe_comp_indicator (s : Finset α) : (↑) ∘ 𝟭_[ℝ≥0] s = 𝟭_[ℝ] s := by
  ext; exact coe_indicator _ _

end NNReal

namespace Complex

@[simp, norm_cast] lemma ofReal_indicator (s : Finset α) (x : α) : ↑(𝟭_[ℝ] s x) = 𝟭_[ℂ] s x :=
  map_indicator ofRealHom _ _

@[simp] lemma ofReal_comp_indicator (s : Finset α) : (↑) ∘ 𝟭_[ℝ] s = 𝟭_[ℂ] s := by
  ext; exact ofReal_indicator _ _

end Complex

/-! ### Normalised indicator -/

namespace Complex
variable (s : Finset α) (a : α)

@[simp, norm_cast] lemma ofReal_mu : ↑(μ_[ℝ] s a) = μ_[ℂ] s a := map_mu (algebraMap ℝ ℂ) ..
@[simp] lemma ofReal_comp_mu : (↑) ∘ μ_[ℝ] s = μ_[ℂ] s := funext <| ofReal_mu _

end Complex

namespace RCLike
variable {𝕜 : Type*} [RCLike 𝕜] (s : Finset α) (a : α)

@[simp, norm_cast] lemma coe_mu : ↑(μ_[ℝ] s a) = μ_[𝕜] s a := map_mu (algebraMap ℝ 𝕜) _ _
@[simp] lemma coe_comp_mu : (↑) ∘ μ_[ℝ] s = μ_[𝕜] s := funext <| coe_mu _

end RCLike

namespace NNReal
open scoped NNReal

@[simp, norm_cast]
lemma coe_mu (s : Finset α) (x : α) : ↑(μ_[ℝ≥0] s x) = μ_[ℝ] s x := map_mu NNReal.toRealHom _ _

@[simp] lemma coe_comp_mu (s : Finset α) : (↑) ∘ μ_[ℝ≥0] s = μ_[ℝ] s := funext <| coe_mu _

end NNReal
