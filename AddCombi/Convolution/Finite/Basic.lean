module

public import AddCombi.Convolution.Finite.Discrete.Defs
public import APAP.Prereqs.Function.Indicator.Defs

import APAP.Prereqs.Function.Indicator.Basic
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Group.Pointwise.Finset.BigOperators
import Mathlib.Analysis.Complex.Order

/-!
# Convolution

This file defines several versions of the discrete convolution of functions.

## Main declarations

* `conv`: Discrete convolution of two functions
* `dconv`: Discrete difference convolution of two functions
* `iterConv`: Iterated convolution of a function

## Notation

* `f ∗ g`: Convolution
* `f ○ g`: Difference convolution
* `f ∗^ n`: Iterated convolution

## Notes

Some lemmas could technically be generalised to a non-commutative semiring domain. Doesn't seem very
useful given that the codomain in applications is either `ℝ`, `ℝ≥0` or `ℂ`.

Similarly we could drop the commutativity assumption on the domain, but this is unneeded at this
point in time.

## TODO

Multiplicativise? Probably ugly and not very useful.
-/

@[expose] public section

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

open Finset Fintype Function
open scoped BigOperators ComplexConjugate NNReal Pointwise translate mu

variable {G R γ : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

/-!
### Convolution of functions

In this section, we define the convolution `f ∗ g` and difference convolution `f ○ g` of functions
`f g : G → R`, and show how they interact.
-/

section CommSemiring
variable [CommSemiring R] {f g : G → R}

lemma indicator_conv_indicator_eq_sum (s t : Finset G) (a : G) :
    (𝟭_[s, R] ∗ 𝟭 t) a = #{x ∈ s ×ˢ t | x.1 + x.2 = a} := by
  simp only [conv_apply, indicator_apply, ← ite_and, filter_comm, boole_mul, sum_boole]
  simp_rw [← mem_product, filter_univ_mem]

lemma indicator_conv (s : Finset G) (f : G → R) : 𝟭_[s] ∗ f = ∑ a ∈ s, τ a f := by
  ext; simp [conv_eq_sum_sub', indicator_apply]

lemma conv_indicator (f : G → R) (s : Finset G) : f ∗ 𝟭_[s] = ∑ a ∈ s, τ a f := by
  ext; simp [conv_eq_sum_sub, indicator_apply]

lemma indicator_conv_indicator_eq_card_vadd_inter_neg (s t : Finset G) (a : G) :
    (𝟭_[s, R] ∗ 𝟭 t) a = #((-a +ᵥ s) ∩ -t) := by
  rw [← card_neg, neg_inter]
  simp [conv_indicator, indicator, inter_comm, ← filter_mem_eq_inter, ← neg_vadd_mem_iff,
    ← sub_eq_add_neg]

variable [StarRing R]

lemma indicator_dconv_indicator_apply (s t : Finset G) (a : G) :
    (𝟭_[s, R] ○ 𝟭 t) a = #{x ∈ s ×ˢ t | x.1 - x.2 = a} := by
  simp only [dconv_apply, indicator_apply, ← ite_and, filter_comm, boole_mul, sum_boole,
    apply_ite conj, map_one, map_zero, Pi.conj_apply]
  simp_rw [← mem_product, filter_univ_mem]

lemma indicator_dconv (s : Finset G) (f : G → R) : 𝟭_[s] ○ f = ∑ a ∈ s, τ a (conjneg f) := by
  ext; simp [dconv_eq_sum_sub', indicator_apply]

lemma dconv_indicator (f : G → R) (s : Finset G) : f ○ 𝟭_[s] = ∑ a ∈ s, τ (-a) f := by
  ext; simp [dconv_eq_sum_add, indicator_apply]

end CommSemiring

section Semifield
variable [Semifield R]

@[simp] lemma mu_univ_conv_mu_univ : μ_[R] (univ : Finset G) ∗ μ univ = μ univ := by
  ext; cases eq_or_ne (card G : R) 0 <;> simp [mu_apply, conv_eq_sum_add, card_univ, *]

lemma mu_conv (s : Finset G) (f : G → R) : μ s ∗ f = (#s : R)⁻¹ • ∑ a ∈ s, τ a f := by
  simp [mu, indicator_conv, smul_conv]

lemma conv_mu (f : G → R) (s : Finset G) : f ∗ μ s = (#s : R)⁻¹ • ∑ a ∈ s, τ a f := by
  simp [mu, conv_indicator, conv_smul]

variable [StarRing R]

@[simp] lemma mu_univ_dconv_mu_univ : μ_[R] (univ : Finset G) ○ μ univ = μ univ := by
  ext; cases eq_or_ne (card G : R) 0 <;> simp [mu_apply, dconv_eq_sum_add, card_univ, *]

lemma mu_dconv (s : Finset G) (f : G → R) :
    μ s ○ f = (#s : R)⁻¹ • ∑ a ∈ s, τ a (conjneg f) := by
  simp [mu, indicator_dconv, smul_dconv]

lemma dconv_mu (f : G → R) (s : Finset G) : f ○ μ s = (#s : R)⁻¹ • ∑ a ∈ s, τ (-a) f := by
  simp [mu, dconv_indicator, dconv_smul]

end Semifield

section Semifield
variable [Semifield R] [CharZero R]

lemma expect_conv (f g : G → R) : 𝔼 a, (f ∗ g) a = (∑ a, f a) * 𝔼 a, g a := by
  simp_rw [expect, sum_conv, mul_smul_comm]

lemma expect_conv' (f g : G → R) : 𝔼 a, (f ∗ g) a = (𝔼 a, f a) * ∑ a, g a := by
  simp_rw [expect, sum_conv, smul_mul_assoc]

variable [StarRing R]

lemma expect_dconv (f g : G → R) : 𝔼 a, (f ○ g) a = (∑ a, f a) * 𝔼 a, conj (g a) := by
  simp_rw [expect, sum_dconv, mul_smul_comm]

lemma expect_dconv' (f g : G → R) : 𝔼 a, (f ○ g) a = (𝔼 a, f a) * ∑ a, conj (g a) := by
  simp_rw [expect, sum_dconv, smul_mul_assoc]

end Semifield

section Field
variable [Field R] [CharZero R]

@[simp] lemma balance_conv (f g : G → R) : balance (f ∗ g) = balance f ∗ balance g := by
  simpa [balance, conv_sub, sub_conv, expect_conv]
    using (mul_smul_comm _ _ _).trans (smul_mul_assoc _ _ _).symm

variable [StarRing R]

@[simp] lemma balance_dconv (f g : G → R) : balance (f ○ g) = balance f ○ balance g := by
  simpa [balance, dconv_sub, sub_dconv, expect_dconv, map_expect]
    using (mul_smul_comm _ _ _).trans (smul_mul_assoc _ _ _).symm

end Field

/-! ### Iterated convolution -/

section CommSemiring
variable [CommSemiring R] {f g : G → R} {n : ℕ}

lemma indicator_iterConv_apply (s : Finset G) :
    ∀ (n : ℕ) (a : G), (𝟭_[s, R] ∗^ n) a = #{x ∈ s ^^ n | ∑ i, x i = a}
  | 0, a => by simp [apply_ite card, eq_comm]
  | n + 1, a => by
    simp_rw [iterConv_succ', conv_eq_sum_sub', indicator_iterConv_apply, indicator_apply, boole_mul,
      sum_ite, filter_univ_mem, sum_const_zero, add_zero, ← Nat.cast_sum, ← Finset.card_sigma]
    congr 1
    refine card_equiv ((Equiv.sigmaEquivProd ..).trans <| Fin.consEquiv fun _ ↦ G) ?_
    aesop (add simp [Fin.sum_cons, Fin.forall_fin_succ])

lemma indicator_iterConv_conv (s : Finset G) (n : ℕ) (f : G → R) :
    𝟭_[s] ∗^ n ∗ f = ∑ a ∈ s ^^ n, τ (∑ i, a i) f := by
  ext b
  simp only [conv_eq_sum_sub', indicator_iterConv_apply, Finset.sum_apply, translate_apply,
    ← nsmul_eq_mul, ← sum_const, Finset.sum_fiberwise']

lemma conv_indicator_iterConv (f : G → R) (s : Finset G) (n : ℕ) :
    f ∗ 𝟭_[s] ∗^ n = ∑ a ∈ s ^^ n, τ (∑ i, a i) f := by
  ext b
  simp only [conv_eq_sum_sub, indicator_iterConv_apply, Finset.sum_apply, translate_apply,
    ← nsmul_eq_mul', ← sum_const, Finset.sum_fiberwise']

variable [StarRing R]

lemma indicator_iterConv_dconv (s : Finset G) (n : ℕ) (f : G → R) :
    𝟭_[s] ∗^ n ○ f = ∑ a ∈ s ^^ n, τ (∑ i, a i) (conjneg f) := by
  rw [← conv_conjneg, indicator_iterConv_conv]

lemma dconv_indicator_iterConv (f : G → R) (s : Finset G) (n : ℕ) :
    f ○ 𝟭_[s] ∗^ n = ∑ a ∈ s ^^ n, τ (-∑ i, a i) f := by
  simp [← conv_conjneg, conjneg_iterConv, conv_indicator_iterConv, piFinset_neg]

end CommSemiring

section Semifield
variable [Semifield R] [CharZero R]

lemma mu_iterConv_conv (s : Finset G) (n : ℕ) (f : G → R) :
    μ s ∗^ n ∗ f = 𝔼 a ∈ piFinset (fun _ : Fin n ↦ s), τ (∑ i, a i) f := by
  simp only [mu, smul_iterConv, inv_pow, smul_conv, indicator_iterConv_conv, expect,
    card_piFinset_const, Nat.cast_pow]
  rw [← NNRat.cast_smul_eq_nnqsmul R]
  push_cast
  rfl

lemma conv_mu_iterConv (f : G → R) (s : Finset G) (n : ℕ) :
    f ∗ μ s ∗^ n = 𝔼 a ∈ piFinset (fun _ : Fin n ↦ s), τ (∑ i, a i) f := by
  rw [conv_comm, mu_iterConv_conv]

variable [StarRing R]

lemma mu_iterConv_dconv (s : Finset G) (n : ℕ) (f : G → R) :
    μ s ∗^ n ○ f = 𝔼 a ∈ piFinset (fun _ : Fin n ↦ s), τ (∑ i, a i) (conjneg f) := by
  rw [← conv_conjneg, mu_iterConv_conv]

lemma dconv_mu_iterConv (f : G → R) (s : Finset G) (n : ℕ) :
    f ○ μ s ∗^ n = 𝔼 a ∈ piFinset (fun _ : Fin n ↦ s), τ (-∑ i, a i) f := by
  simp_rw [← conv_conjneg, conjneg_iterConv, conjneg_mu, conv_mu_iterConv, piFinset_neg,
    expect_neg_index, Pi.neg_apply, sum_neg_distrib]

end Semifield

section Field
variable [Field R] [CharZero R]

@[simp] lemma balance_iterConv (f : G → R) : ∀ {n}, n ≠ 0 → balance (f ∗^ n) = balance f ∗^ n
  | 0, h => by cases h rfl
  | 1, _ => by simp
  | n + 2, _ => by simp [iterConv_succ _ (n + 1), balance_iterConv _ n.succ_ne_zero]

end Field
