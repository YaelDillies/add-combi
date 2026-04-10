module

public import AddCombi.Convolution.Finite.Discrete.Defs
public import APAP.Prereqs.LpNorm.Compact
public import APAP.Prereqs.LpNorm.Discrete.Defs
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.MeasureTheory.Constructions.AddChar

import APAP.Prereqs.Inner.Hoelder.Compact
import APAP.Prereqs.Inner.Hoelder.Discrete
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Discrete Fourier transform

This file defines the discrete Fourier transform and shows the Parseval-Plancherel identity and
Fourier inversion formula for it.
-/

@[expose] public section

open AddChar Finset Fintype Function MeasureTheory RCLike
open scoped BigOperators ComplexConjugate ComplexOrder translate

variable {α γ : Type*} [AddCommGroup α] [Fintype α] {f : α → ℂ} {ψ : AddChar α ℂ} {n : ℕ}

/-- The discrete Fourier transform. -/
noncomputable def dft (f : α → ℂ) : AddChar α ℂ → ℂ := fun ψ ↦ ⟪ψ, f⟫_[ℂ]

lemma dft_apply (f : α → ℂ) (ψ : AddChar α ℂ) : dft f ψ = ⟪ψ, f⟫_[ℂ] := rfl

@[simp] lemma dft_zero : dft (0 : α → ℂ) = 0 := by ext; simp [dft_apply]

@[simp] lemma dft_add (f g : α → ℂ) : dft (f + g) = dft f + dft g := by
  ext; simp [wInner_add_right, dft_apply]

@[simp] lemma dft_neg (f : α → ℂ) : dft (-f) = - dft f := by ext; simp [dft_apply]

@[simp] lemma dft_sub (f g : α → ℂ) : dft (f - g) = dft f - dft g := by
  ext; simp [wInner_sub_right, dft_apply]

@[simp] lemma dft_const (a : ℂ) (hψ : ψ ≠ 0) : dft (const α a) ψ = 0 := by
  simp only [dft_apply, wInner_one_eq_sum, inner_apply', const_apply, ← sum_mul, ← map_sum,
    sum_eq_zero_iff_ne_zero.2 hψ, map_zero, zero_mul]

@[simp]
lemma dft_smul {𝕝 : Type*} [CommSemiring 𝕝] [StarRing 𝕝] [Algebra 𝕝 ℂ] [StarModule 𝕝 ℂ]
    [IsScalarTower 𝕝 ℂ ℂ] (c : 𝕝) (f : α → ℂ) : dft (c • f) = c • dft f := by
  ext; simp [wInner_smul_right, dft_apply]

/-- **Parseval-Plancherel identity** for the discrete Fourier transform. -/
@[simp] lemma wInner_cWeight_dft (f g : α → ℂ) : ⟪dft f, dft g⟫ₙ_[ℂ] = ⟪f, g⟫_[ℂ] := by
  classical
  unfold dft
  simp_rw [wInner_one_eq_sum, wInner_cWeight_eq_expect, inner_apply', map_sum, map_mul,
    starRingEnd_self_apply, sum_mul, mul_sum, expect_sum_comm, mul_mul_mul_comm _ (conj <| f _),
    ← expect_mul, ← AddChar.inv_apply_eq_conj, ← map_neg_eq_inv, ← map_add_eq_mul,
    AddChar.expect_apply_eq_ite, add_neg_eq_zero, boole_mul, Fintype.sum_ite_eq]

/-- **Parseval-Plancherel identity** for the discrete Fourier transform. -/
@[simp] lemma cL2Norm_dft [MeasurableSpace α] [DiscreteMeasurableSpace α] (f : α → ℂ) :
    ‖dft f‖ₙ_[2] = ‖f‖_[2] :=
  (sq_eq_sq₀ lpNorm_nonneg lpNorm_nonneg).1 <| Complex.ofReal_injective <| by
    push_cast; simpa only [RCLike.wInner_cWeight_self, wInner_one_self] using wInner_cWeight_dft f f

/-- **Fourier inversion** for the discrete Fourier transform. -/
lemma dft_inversion (f : α → ℂ) (a : α) : 𝔼 ψ, dft f ψ * ψ a = f a := by
  classical
  simp_rw [dft, wInner_one_eq_sum, inner_apply', sum_mul, expect_sum_comm, mul_right_comm _ (f _),
    ← expect_mul, ← AddChar.inv_apply_eq_conj, inv_mul_eq_div, ← map_sub_eq_div,
    AddChar.expect_apply_eq_ite, sub_eq_zero, boole_mul, Fintype.sum_ite_eq]

/-- **Fourier inversion** for the discrete Fourier transform. -/
lemma dft_inversion' (f : α → ℂ) : 𝔼 ψ, dft f ψ • ⇑ψ = f := by ext; simpa using dft_inversion f _

lemma dft_dft_doubleDualEmb (f : α → ℂ) (a : α) :
    dft (dft f) (doubleDualEmb a) = card α * f (-a) := by
  simp only [← dft_inversion f (-a), dft_apply, wInner_one_eq_sum, inner_apply,
    map_neg_eq_inv, AddChar.inv_apply_eq_conj, doubleDualEmb_apply, ← Fintype.card_mul_expect,
    AddChar.card_eq]

lemma dft_dft (f : α → ℂ) : dft (dft f) = card α * f ∘ doubleDualEquiv.symm ∘ Neg.neg :=
  funext fun a ↦ by
    simp_rw [Pi.mul_apply, Function.comp_apply, map_neg, Pi.natCast_apply, ← dft_dft_doubleDualEmb,
      doubleDualEmb_doubleDualEquiv_symm_apply]

lemma dft_injective : Injective (dft : (α → ℂ) → AddChar α ℂ → ℂ) := fun f g h ↦
  funext fun a ↦ (dft_inversion _ _).symm.trans <| by rw [h, dft_inversion]

lemma dft_inv (ψ : AddChar α ℂ) (hf : IsSelfAdjoint f) : dft f ψ⁻¹ = conj (dft f ψ) := by
  simp_rw [dft_apply, wInner_one_eq_sum, inner_apply, map_sum, AddChar.inv_apply', map_mul,
    AddChar.inv_apply_eq_conj, Complex.conj_conj, (hf.apply _).conj_eq]

@[simp]
lemma dft_conj (f : α → ℂ) (ψ : AddChar α ℂ) : dft (conj f) ψ = conj (dft f ψ⁻¹) := by
  simp only [dft_apply, wInner_one_eq_sum, inner_apply, map_sum, map_mul, ← inv_apply',
    ← inv_apply_eq_conj, inv_inv, Pi.conj_apply]

lemma dft_conjneg_apply (f : α → ℂ) (ψ : AddChar α ℂ) : dft (conjneg f) ψ = conj (dft f ψ) := by
  simp only [dft_apply, wInner_one_eq_sum, inner_apply, conjneg_apply, map_sum, map_mul,
    RCLike.conj_conj]
  refine Fintype.sum_equiv (Equiv.neg α) _ _ fun i ↦ ?_
  simp only [Equiv.neg_apply, ← inv_apply_eq_conj, ← inv_apply', inv_apply]

@[simp]
lemma dft_conjneg (f : α → ℂ) : dft (conjneg f) = conj (dft f) := funext <| dft_conjneg_apply _

lemma dft_comp_neg_apply (f : α → ℂ) (ψ : AddChar α ℂ) :
    dft (fun x ↦ f (-x)) ψ = dft f (-ψ) := Fintype.sum_equiv (Equiv.neg _) _ _ (by simp)

@[simp] lemma dft_balance (f : α → ℂ) (hψ : ψ ≠ 0) : dft (balance f) ψ = dft f ψ := by
  simp only [balance, Pi.sub_apply, dft_sub, dft_const _ hψ, sub_zero]

@[simp] lemma dft_trivChar [DecidableEq α] : dft (trivChar : α → ℂ) = 1 := by
  ext; simp [trivChar_apply, dft_apply, wInner_one_eq_sum]

@[simp] lemma dft_one : dft (1 : α → ℂ) = card α • trivChar :=
  dft_injective <| by classical rw [dft_smul, dft_trivChar, dft_dft, Pi.one_comp, nsmul_eq_mul]

variable [DecidableEq α]

@[simp] lemma dft_indicator_zero (A : Finset α) : dft (𝟭 A) 0 = #A := by
  simp only [dft_apply, wInner_one_eq_sum, inner_apply', sum_indicator, AddChar.zero_apply, map_one,
    one_mul]

lemma dft_conv_apply (f g : α → ℂ) (ψ : AddChar α ℂ) : dft (f ∗ g) ψ = dft f ψ * dft g ψ := by
  simp_rw [dft, wInner_one_eq_sum, inner_apply, conv_eq_sum_sub', mul_sum, sum_mul, ← sum_product',
    univ_product_univ]
  refine Fintype.sum_equiv ((Equiv.prodComm _ _).trans <|
    ((Equiv.refl _).prodShear Equiv.subRight).trans <| Equiv.prodComm _ _)  _ _ fun (a, b) ↦ ?_
  simp [mul_mul_mul_comm, ← map_mul, ← map_add_eq_mul]

lemma dft_dconv_apply (f g : α → ℂ) (ψ : AddChar α ℂ) :
    dft (f ○ g) ψ = dft f ψ * conj (dft g ψ) := by
  rw [← conv_conjneg, dft_conv_apply, dft_conjneg_apply]

@[simp] lemma dft_conv (f g : α → ℂ) : dft (f ∗ g) = dft f * dft g := funext <| dft_conv_apply _ _

@[simp]
lemma dft_dconv (f g : α → ℂ) : dft (f ○ g) = dft f * conj (dft g) := funext <| dft_dconv_apply _ _

@[simp] lemma dft_iterConv (f : α → ℂ) : ∀ n, dft (f ∗^ n) = dft f ^ n
  | 0 => dft_trivChar
  | n + 1 => by simp [iterConv_succ, pow_succ, dft_iterConv]

@[simp] lemma dft_iterConv_apply (f : α → ℂ) (n : ℕ) (ψ : AddChar α ℂ) :
    dft (f ∗^ n) ψ = dft f ψ ^ n := congr_fun (dft_iterConv _ _) _
