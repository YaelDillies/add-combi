/-
Copyright (c) 2023 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described ∈ the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import AddCombi.Mathlib.Combinatorics.Additive.Energy
-- FIXME: This public import shouldn't be needed.
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic

import AddCombi.Convolution.Finite.Order
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.Finset.CastCard
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.Positivity.Finset

open Finset
open scoped BigOperators ComplexConjugate Pointwise Combinatorics.Additive' Indicator

section
variable {α : Type*} [DecidableEq α] {H : Finset (α × α)} {A B X : Finset α} {x : α}

noncomputable def oneOfPair (H : Finset (α × α)) (X : Finset α) : Finset α :=
  {x ∈ X | (3 / 4 : ℝ) * #X ≤ #{yz ∈ H | yz.1 = x}}

lemma oneOfPair_mem : x ∈ oneOfPair H X ↔ x ∈ X ∧ (3 / 4 : ℝ) * #X ≤ #{yz ∈ H | yz.1 = x} :=
  mem_filter

lemma oneOfPair_mem' (hH : H ⊆ X ×ˢ X) : #{yz ∈ H | yz.1 = x} = #{c ∈ X | (x, c) ∈ H} := by
  refine card_nbij' Prod.snd (fun c ↦ (x, c)) ?_ (by simp [Set.MapsTo])
    (by aesop (add simp [Set.LeftInvOn])) (by simp [Set.LeftInvOn])
  simpa +contextual [Set.MapsTo, eq_comm] using fun a b hab _ ↦ (mem_product.1 (hH hab)).2

lemma oneOfPair_bound_one :
    ∑ x ∈ X \ oneOfPair H X, (#{yz ∈ H | yz.1 = x} : ℝ) ≤ (3 / 4) * #X ^ 2 :=
  calc _ ≤ ∑ _x ∈ X \ oneOfPair H X, (3 / 4 : ℝ) * #X := by
        gcongr with i hi
        simp only [oneOfPair, ← filter_not, not_le, mem_filter] at hi
        exact hi.2.le
       _ = #(X \ oneOfPair H X) * ((3 / 4 : ℝ) * #X) := by simp
       _ ≤ #X * ((3 / 4 : ℝ) * #X) := by gcongr; exact sdiff_subset
       _ = _ := by ring

lemma oneOfPair_bound_two (hH : H ⊆ X ×ˢ X) (Hcard : (7 / 8 : ℝ) * #X ^ 2 ≤ #H) :
    (1 / 8 : ℝ) * #X ^ 2 ≤ #X * #(oneOfPair H X) :=
  calc _ = (7 / 8 : ℝ) * #X ^ 2 - 3 / 4 * #X ^ 2 := by ring
       _ ≤ #H - (3 / 4 : ℝ) * #X ^ 2 := by linarith
       _ ≤ #H - ∑ x ∈ X \ oneOfPair H X, (#{yz ∈ H | yz.1 = x} : ℝ) := by
        gcongr; exact oneOfPair_bound_one
       _ = #H - ∑ x ∈ X, (#{yz ∈ H | yz.1 = x} : ℝ) +
              ∑ x ∈ oneOfPair H X, (#{yz ∈ H | yz.1 = x} : ℝ) := by
        rw [sum_sdiff_eq_sub, sub_add]; exact filter_subset ..
       _ = ∑ x ∈ oneOfPair H X, (#{yz ∈ H | yz.1 = x} : ℝ) := by
        rw [add_eq_right, sub_eq_zero, ← Nat.cast_sum, Nat.cast_inj, ← card_eq_sum_card_fiberwise]
        exact fun x hx ↦ (mem_product.1 (hH hx)).1
       _ ≤ ∑ _x ∈ oneOfPair H X, (#X : ℝ) := by
        simp_rw [oneOfPair_mem' hH]; gcongr with i; exact filter_subset ..
       _ = #X * #(oneOfPair H X) := by simp [mul_comm]

private lemma oneOfPair_bound {K : ℝ} (hH : H ⊆ X ×ˢ X) (hX : (0 : ℝ) < #X)
    (Hcard : (7 / 8 : ℝ) * #X ^ 2 ≤ #H) (h : #A / (2 * K) ≤ #X) :
    #A / (2 ^ 4 * K) ≤ #(oneOfPair H X) := -- by
  calc
    _ = (#A / (2 * K)) / 8 := by ring
    _ ≤ (#X / 8 : ℝ) := by gcongr
    _ ≤ #(oneOfPair H X) :=
      le_of_mul_le_mul_left ((oneOfPair_bound_two hH Hcard).trans_eq' (by ring)) hX

lemma quadruple_bound_c {a b : α} {H : Finset (α × α)} (ha : a ∈ oneOfPair H X)
    (hb : b ∈ oneOfPair H X) (hH : H ⊆ X ×ˢ X) :
    (#X : ℝ) / 2 ≤ #{c ∈ X | (a, c) ∈ H ∧ (b, c) ∈ H} := by
  rw [oneOfPair_mem, oneOfPair_mem' hH] at ha hb
  rw [filter_and, cast_card_inter, ← filter_or]
  have : (#{c ∈ X | (a, c) ∈ H ∨ (b, c) ∈ H} : ℝ) ≤ #X := by gcongr; exact filter_subset ..
  linarith [ha.2, hb.2, this]

variable [AddCommGroup α]

lemma quadruple_bound_right {a b : α} (H : Finset (α × α)) (X : Finset α) (h : x = a - b) :
    (#({c ∈ X | (a, c) ∈ H ∧ (b, c) ∈ H}.sigma fun c ↦ ((B ×ˢ B) ×ˢ B ×ˢ B).filter
        fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c) : ℝ)
      ≤ #(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ (a₁ - a₂) - (a₃ - a₄) = a - b) := by
  rw [← h, Nat.cast_le]
  refine card_le_card_of_injOn Sigma.snd (by simp +contextual [Set.MapsTo, *]) ?_
  simp +contextual [Set.InjOn]
  aesop

end

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {K : Type*} [Semifield K] [CharZero K] [StarRing K]
variable {A B : Finset G} {x : G}

lemma thing_three : 𝔼 x, (𝟭_[(A : Set G), K] ○ 𝟭_[B]) x ^ 2 = E[A, B] := by
  simp only [indicator_one_dconv_indicator_one_eq_dens, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, expect_mul,
    sum_filter, Nat.cast_ite, Nat.cast_zero, sum_product, sq, addEnergy, mul_expect]
  simp only [mul_boole, sum_comm (s := univ), sum_ite_eq, mem_univ, ite_true]
  simp only [sum_comm (s := B) (t := A), sub_eq_sub_iff_add_eq_add]
  exact sum_comm

section lemma1

lemma claim_one : ∑ s, (𝟭_[(A : Set G), K] ○ 𝟭_[B]) s * #(A ∩ (s +ᵥ B)) = E[A, B] := by
  simp only [← thing_three, ← indicator_one_dconv_indicator_one_eq_dens, sq]

lemma claim_two :
    (E[A, B]) ^ 2 / (#A * #B) ≤ ∑ s, (𝟭_[A, ℝ] ○ 𝟭_[B]) s * #(A ∩ (s +ᵥ B)) ^ 2 := by
  let f := fun s ↦ ((𝟭_[A, ℝ] ○ 𝟭_[B]) s).sqrt
  have hf : ∀ s, f s ^ 2 = (𝟭_[A, ℝ] ○ 𝟭_[B]) s := by
    intro s
    rw [Real.sq_sqrt]
    exact dconv_apply_nonneg indicator_nonneg indicator_nonneg s
  have := sum_mul_sq_le_sq_mul_sq univ f (fun s ↦ f s * #(A ∩ (s +ᵥ B)))
  refine div_le_of_le_mul₀ (by positivity) ?_ ?_
  · refine sum_nonneg fun i _ ↦ ?_
    -- indicator nonneg should be a positivity lemma
    exact mul_nonneg (dconv_apply_nonneg indicator_nonneg indicator_nonneg _) (by positivity)
  simp only [← sq, ← mul_assoc, hf, thing_two, mul_pow, claim_one] at this
  refine this.trans ?_
  rw [mul_comm]

lemma claim_three {H : Finset (G × G)} (hH : H ⊆ A ×ˢ A) :
    ∑ s, (𝟭_[A, ℝ] ○ 𝟭_[B]) s * #((A ∩ (s +ᵥ B)) ×ˢ (A ∩ (s +ᵥ B)) ∩ H) =
      ∑ ab ∈ H, ∑ s, (𝟭_[A, ℝ] ○ 𝟭_[B]) s * (𝟭_[B] (ab.1 - s) * 𝟭_[B] (ab.2 - s)) := by
  simp only [sum_comm (s := H), ← mul_sum]
  refine sum_congr rfl fun x _ ↦ ?_
  congr 1
  rw [card_eq_sum_ones, inter_comm, ← filter_mem_eq_inter, sum_filter, Nat.cast_sum]
  refine sum_congr rfl fun ⟨a, b⟩ hab ↦ ?_
  have : a ∈ A ∧ b ∈ A := by simpa using hH hab
  simp only [mem_inter, mem_product, Nat.cast_ite, Nat.cast_zero, Nat.cast_one, this, true_and,
    indicator_apply, ite_and, boole_mul, ← neg_vadd_mem_iff, vadd_eq_add, neg_add_eq_sub]

lemma claim_four (ab : G × G) :
  ∑ s, (𝟭_[A, ℝ] ○ 𝟭_[B]) s * (𝟭_[B] (ab.1 - s) * 𝟭_[B] (ab.2 - s)) ≤
    #B * (𝟭_[B] ○ 𝟭_[B]) (ab.1 - ab.2) := by
  rcases ab with ⟨a, b⟩
have : ∀ s, (𝟭_[A, ℝ] ○ 𝟭_[B]) s ≤ #B := fun s ↦ by
    simp only [dconv_eq_sum_add, conj_indicator_apply, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    simp only [indicator_apply, mul_boole, ← sum_filter (· ∈ B), filter_mem_eq_inter, univ_inter]
    refine sum_le_sum fun i _ ↦ ?_
    split
    · rfl
    · exact zero_le_one
have : ∑ s : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) s * (𝟭_[B] ((a, b).1 - s) * 𝟭_[B] ((a, b).2 - s)) ≤
    #B * ∑ s : G, (𝟭_[B] ((a, b).1 - s) * 𝟭_[B] ((a, b).2 - s)) := by
    rw [mul_sum]
    gcongr with s hs
    · exact mul_nonneg indicator_apply_nonneg indicator_apply_nonneg
    · exact this _
  refine this.trans_eq ?_
  congr 1
  simp only [dconv_eq_sum_add]
  exact Fintype.sum_equiv (Equiv.subLeft b) _ _ <| by simp

lemma claim_five {H : Finset (G × G)} (hH : H ⊆ A ×ˢ A) :
  ∑ s, (𝟭_[A, ℝ] ○ 𝟭_[B]) s * #((A ∩ (s +ᵥ B)) ×ˢ (A ∩ (s +ᵥ B)) ∩ H) ≤
    #B * ∑ ab ∈ H, (𝟭_[B] ○ 𝟭_[B]) (ab.1 - ab.2) := by
  rw [claim_three hH, mul_sum]
  exact sum_le_sum fun ab _ ↦ claim_four ab

noncomputable def H_choice (A B : Finset G) (c : ℝ) : Finset (G × G) :=
{ab ∈ A ×ˢ A | (𝟭_[ℝ] B ○ 𝟭_[B]) (ab.1 - ab.2) ≤ c / 2 * (E[A, B] ^ 2 / (#A ^ 3 * #B ^ 2))}

lemma claim_six (c : ℝ) (hc : 0 ≤ c) :
  ∑ s, (𝟭_[A, ℝ] ○ 𝟭_[B]) s * #((A ∩ (s +ᵥ B)) ×ˢ (A ∩ (s +ᵥ B)) ∩ H_choice A B c) ≤
      c / 2 * (E[A, B] ^ 2 / (#A * #B)) := by
  refine (claim_five (filter_subset _ _)).trans ?_
  have : ∑ ab ∈ H_choice A B c, (𝟭_[ℝ] B ○ 𝟭_[B]) (ab.1 - ab.2) ≤
      #(H_choice A B c) * (c / 2 * (E[A, B] ^ 2 / (#A ^ 3 * #B ^ 2))) := by
    rw [← nsmul_eq_mul]
    exact sum_le_card_nsmul _ _ _ fun x hx ↦ (mem_filter.1 hx).2
  have hA : (#(H_choice A B c) : ℝ) ≤ #A ^ 2 := by
    norm_cast
    exact (card_le_card (filter_subset _ _)).trans_eq (by simp [sq])
  refine (mul_le_mul_of_nonneg_left this (by positivity)).trans ?_
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  obtain rfl | hA := B.eq_empty_or_nonempty
  · simp
  calc
    _ ≤ (#B : ℝ) * (#A ^ 2 * (c / 2 * (E[A, B] ^ 2 / (#A ^ 3 * #B ^ 2)))) := by gcongr
    _ = c / 2 * (E[A, B] ^ 2 / (#A * #B)) := by field_simp

lemma claim_seven (c : ℝ) (hc : 0 ≤ c) (hA : (0 : ℝ) < #A) (hB : (0 : ℝ) < #B) :
  ∑ s, (𝟭_[A, ℝ] ○ 𝟭_[B]) s *
        ((c / 2) * (E[A, B] ^ 2 / (#A ^ 2 * #B ^ 2)) +
          #((A ∩ (s +ᵥ B)) ×ˢ (A ∩ (s +ᵥ B)) ∩ H_choice A B c)) ≤
    ∑ s, (𝟭_[A, ℝ] ○ 𝟭_[B]) s * (c * #(A ∩ (s +ᵥ B)) ^ 2) :=
  calc
    _ = (c / 2 * (E[A, B] ^ 2 / (#A * #B))) +
        ∑ x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * #((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ H_choice A B c) := by
        simp only [mul_add, sum_add_distrib, ← sum_mul, thing_two, ← mul_pow]
        field_simp
    _ ≤ _ := by
      grw [claim_six c hc, ← add_mul, add_halves]
      simp only [mul_left_comm _ c, ← mul_sum]
      gcongr
      exact claim_two

lemma claim_eight (c : ℝ) (hc : 0 ≤ c) (hA : (0 : ℝ) < #A) (hB : (0 : ℝ) < #B) :
    ∃ s : G, ((c / 2) * (E[A, B] ^ 2 / (#A ^ 2 * #B ^ 2)) +
          #((A ∩ (s +ᵥ B)) ×ˢ (A ∩ (s +ᵥ B)) ∩ H_choice A B c)) ≤
      c * #(A ∩ (s +ᵥ B)) ^ 2 := by
  by_contra!
  refine (claim_seven c hc hA hB).not_gt ?_
  refine sum_lt_sum ?_ ?_
  · intros s _
    exact mul_le_mul_of_nonneg_left (this s).le (dconv_nonneg indicator_nonneg indicator_nonneg s)
have : 0 < 𝟭_[A, ℝ] ○ 𝟭_[B] := by
    refine dconv_pos ?_ ?_
    · simpa [indicator_pos, Finset.card_pos] using hA
    · simpa [indicator_pos, Finset.card_pos] using hB
  rw [@Pi.lt_def] at this
  obtain ⟨-, i, hi : 0 < _⟩ := this
  exact ⟨i, by simp, mul_lt_mul_of_pos_left (this i) hi⟩

lemma test_case {E A B : ℕ} {K : ℝ} (hK : 0 < K) (hE : K⁻¹ * (A ^ 2 * B) ≤ E)
    (hA : 0 < A) (hB : 0 < B) :
    A / (Real.sqrt 2 * K) ≤ Real.sqrt 2⁻¹ * (E / (A * B)) := by
  rw [inv_mul_le_iff₀ hK] at hE
  rw [mul_div_assoc', div_le_div_iff₀, ← mul_assoc, ← sq]
  rotate_left
  · positivity
  · positivity
  refine hE.trans_eq ?_
  field_simp
  simp

lemma lemma_one {c K : ℝ} (hc : 0 < c) (hK : 0 < K) (hE : K⁻¹ * (#A ^ 2 * #B) ≤ E[A, B])
    (hA : (0 : ℝ) < #A) (hB : (0 : ℝ) < #B) :
    ∃ s : G, ∃ X ⊆ A ∩ (s +ᵥ B), #A / (Real.sqrt 2 * K) ≤ #X ∧
      (1 - c) * #X ^ 2 ≤
      #((X ×ˢ X).filter fun ⟨a, b⟩ ↦ c / 2 * (K ^ 2)⁻¹ * #A ≤ (𝟭_[B] ○ 𝟭_[B]) (a - b)) := by
  obtain ⟨s, hs⟩ := claim_eight c hc.le hA hB
  set X := A ∩ (s +ᵥ B)
  refine ⟨s, X, subset_rfl, ?_, ?_⟩
  · have : (2 : ℝ)⁻¹ * (E[A, B] / (#A * #B)) ^ 2 ≤ card X ^ 2 := by
      refine le_of_mul_le_mul_left ?_ hc
      exact ((le_add_of_nonneg_right (Nat.cast_nonneg _)).trans hs).trans_eq' (by ring)
    replace := Real.sqrt_le_sqrt this
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
      Real.sqrt_sq (by positivity)] at this
    refine this.trans' ?_
    -- I'd like automation to handle the rest of this
    rw [inv_mul_le_iff₀ hK] at hE
    rw [mul_div_assoc', div_le_div_iff₀, ← mul_assoc, ← sq]
    rotate_left
    · positivity
    · positivity
    refine hE.trans_eq ?_
    field_simp
    simp
  rw [one_sub_mul, sub_le_comm]
  refine ((le_add_of_nonneg_left (by positivity)).trans hs).trans' ?_
  rw [sq, ← Nat.cast_mul, ← card_product, ← cast_card_sdiff (filter_subset _ _), ← filter_not,
    ← filter_mem_eq_inter]
  gcongr ↑(#?_)
  rintro ⟨a, b⟩
  simp +contextual only [not_le, mem_product, mem_inter, and_imp, mem_filter, H_choice, and_self,
    true_and, X]
  rintro _ _ _ _ h
  grw [h, ← hE]
  apply le_of_eq
  field_simp [hA, hB, hK, le_div_iff₀, div_le_iff₀] at hE ⊢

lemma lemma_one' {c K : ℝ} (hc : 0 < c) (hK : 0 < K)
    (hE : K⁻¹ * (#A ^ 2 * #B) ≤ E[A, B])
    (hA : (0 : ℝ) < #A) (hB : (0 : ℝ) < #B) :
    ∃ s : G, ∃ X ⊆ A ∩ (s +ᵥ B), #A / (2 * K) ≤ #X ∧
      (1 - c) * #X ^ 2 ≤
      #((X ×ˢ X).filter fun ⟨a, b⟩ ↦ c / 2 * (K ^ 2)⁻¹ * #A ≤ (𝟭_[B] ○ 𝟭_[B]) (a - b)) := by
  obtain ⟨s, X, hX₁, hX₂, hX₃⟩ := lemma_one hc hK hE hA hB
  refine ⟨s, X, hX₁, hX₂.trans' ?_, hX₃⟩
  gcongr _ / (?_ * _)
  rw [Real.sqrt_le_iff]
  norm_num

end lemma1

section lemma2

open Pointwise

lemma many_pairs {K : ℝ} {x : G} (hab : (1 / 8 : ℝ) / 2 * (K ^ 2)⁻¹ * #A ≤ (𝟭_[B] ○ 𝟭_[B]) x) :
    #A / (2 ^ 4 * K ^ 2) ≤ #((B ×ˢ B).filter fun ⟨c, d⟩ ↦ c - d = x) :=
  calc
    _ = (1 / 8 : ℝ) / 2 * (K ^ 2)⁻¹ * #A := by ring
  _ ≤ (𝟭_[B] ○ 𝟭_[B]) x := hab
    _ ≤ #((B ×ˢ B).filter fun ⟨c, d⟩ ↦ c - d = x) := by rw [indicator_dconv_indicator_apply]

variable {H : Finset (G × G)} {X : Finset G}

lemma quadruple_bound_part {K : ℝ} (a c : G)
  (hac : (1 / 8 : ℝ) / 2 * (K ^ 2)⁻¹ * #A ≤ (𝟭_[B] ○ 𝟭_[B]) (a - c)) :
    #A / (2 ^ 4 * K ^ 2) ≤ #((B ×ˢ B).filter fun ⟨a₁, a₂⟩ ↦ a₁ - a₂ = a - c) :=
  many_pairs hac

lemma quadruple_bound_other {a b c : G} {K : ℝ} {H : Finset (G × G)}
    (hac : (a, c) ∈ H) (hbc : (b, c) ∈ H)
  (hH : ∀ x ∈ H, (1 / 8 : ℝ) / 2 * (K ^ 2)⁻¹ * #A ≤ (𝟭_[B] ○ 𝟭_[B]) (x.1 - x.2)) :
    (#A / (2 ^ 4 * K ^ 2)) ^ 2 ≤ #(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦
        a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c) := by
  change (_ : ℝ) ≤ #(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun (z : (G × G) × G × G) ↦
    z.1.1 - z.1.2 = a - c ∧ z.2.1 - z.2.2 = b - c)
  rw [filter_product (s := B ×ˢ B) (t := B ×ˢ B) (fun z ↦ z.1 - z.2 = a - c)
    (fun z ↦ z.1 - z.2 = b - c), card_product, sq, Nat.cast_mul]
  gcongr ?_ * ?_
  · exact quadruple_bound_part _ _ (hH _ hac)
  · exact quadruple_bound_part _ _ (hH _ hbc)

lemma quadruple_bound_left {a b : G} {K : ℝ} {H : Finset (G × G)}
    (ha : a ∈ oneOfPair H X) (hb : b ∈ oneOfPair H X)
  (hH : ∀ x ∈ H, (1 / 8 : ℝ) / 2 * (K ^ 2)⁻¹ * #A ≤ (𝟭_[B] ○ 𝟭_[B]) (x.1 - x.2))
    (hH' : H ⊆ X ×ˢ X) :
    #X / 2 * (#A / (2 ^ 4 * K ^ 2)) ^ 2 ≤
      #({c ∈ X | (a, c) ∈ H ∧ (b, c) ∈ H}.sigma fun c ↦
      ((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦
        a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c) :=
  calc
    _ ≤ ∑ c ∈ X with (a, c) ∈ H ∧ (b, c) ∈ H, ((#A / (2 ^ 4 * K ^ 2)) ^ 2 : ℝ) := by
      rw [sum_const, nsmul_eq_mul]
      gcongr ?_ * _
      exact quadruple_bound_c ha hb hH'
    _ ≤ ∑ c ∈ X with (a, c) ∈ H ∧ (b, c) ∈ H, (#(((B ×ˢ B) ×ˢ B ×ˢ B).filter
        fun ((a₁, a₂), a₃, a₄) ↦ a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c) : ℝ) := by
      gcongr with i hi
      simp only [mem_filter] at hi
      exact quadruple_bound_other hi.2.1 hi.2.2 hH
    _ = _ := by rw [card_sigma, Nat.cast_sum]

lemma quadruple_bound {K : ℝ} {x : G} (hx : x ∈ oneOfPair H X - oneOfPair H X)
  (hH : ∀ x ∈ H, (1 / 8 : ℝ) / 2 * (K ^ 2)⁻¹ * #A ≤ (𝟭_[B] ○ 𝟭_[B]) (x.1 - x.2))
    (hH' : H ⊆ X ×ˢ X) :
    (#A ^ 2 * #X) / (2 ^ 9 * K ^ 4) ≤
      #(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ (a₁ - a₂) - (a₃ - a₄) = x) := by
  rw [mem_sub] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  refine (quadruple_bound_right H X rfl).trans' ?_
  refine (quadruple_bound_left ha hb hH hH').trans_eq' ?_
  ring

lemma big_quadruple_bound {K : ℝ}
  (hH : ∀ x ∈ H, (1 / 8 : ℝ) / 2 * (K ^ 2)⁻¹ * #A ≤ (𝟭_[B] ○ 𝟭_[B]) (x.1 - x.2))
    (hH' : H ⊆ X ×ˢ X)
    (hX : #A / (2 * K) ≤ #X) :
    (#(oneOfPair H X - oneOfPair H X)) * (#A ^ 3 / (2 ^ 10 * K ^ 5)) ≤ #B ^ 4 :=
  calc
    _ = (#(oneOfPair H X - oneOfPair H X)) * ((#A ^ 2 * (#A / (2 * K))) / (2 ^ 9 * K ^ 4)) := by
      ring
    _ ≤ (#(oneOfPair H X - oneOfPair H X)) * ((#A ^ 2 * #X) / (2 ^ 9 * K ^ 4)) := by gcongr
    _ = ∑ _x ∈ oneOfPair H X - oneOfPair H X, ((#A ^ 2 * #X) / (2 ^ 9 * K ^ 4) : ℝ) := by simp
    _ ≤ ∑ x ∈ oneOfPair H X - oneOfPair H X,
          (#(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ (a₁ - a₂) - (a₃ - a₄) = x) : ℝ) :=
      sum_le_sum fun x hx ↦ quadruple_bound hx hH hH'
    _ ≤ ∑ x, (#(((B ×ˢ B) ×ˢ B ×ˢ B).filter
          fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ (a₁ - a₂) - (a₃ - a₄) = x) : ℝ) := by
      gcongr; exact subset_univ _
    _ = _ := by
      rw [← Nat.cast_sum, ← card_eq_sum_card_fiberwise]
      · simp only [card_product, Nat.cast_mul]
        ring_nf
      · simp [Set.MapsTo]

omit [Fintype G]
variable [Finite G]

theorem BSG_aux {K : ℝ} (hK : 0 < K) (hA : (0 : ℝ) < #A) (hB : (0 : ℝ) < #B)
    (hAB : K⁻¹ * (#A ^ 2 * #B) ≤ E[A, B]) :
    ∃ s : G, ∃ A' ⊆ A ∩ (s +ᵥ B), (2 ^ 4)⁻¹ * K⁻¹ * #A ≤ #A' ∧
    #(A' - A') ≤ 2 ^ 10 * K ^ 5 * #B ^ 4 / #A ^ 3 := by
  cases nonempty_fintype G
  obtain ⟨s, X, hX₁, hX₂, hX₃⟩ := lemma_one' (c := 1 / 8) (by norm_num) hK hAB hA hB
  set H : Finset (G × G) := (X ×ˢ X).filter
  fun ⟨a, b⟩ ↦ (1 / 8 : ℝ) / 2 * (K ^ 2)⁻¹ * #A ≤ (𝟭_[B] ○ 𝟭_[B]) (a - b)
  have : (0 : ℝ) < #X := hX₂.trans_lt' (by positivity)
  refine ⟨s, oneOfPair H X, (filter_subset _ _).trans hX₁, ?_, ?_⟩
  · rw [← mul_inv, inv_mul_eq_div]
    exact oneOfPair_bound (filter_subset _ _) this (hX₃.trans_eq' (by norm_num)) hX₂
  have := big_quadruple_bound (H := H) (fun x hx ↦ (mem_filter.1 hx).2) (filter_subset _ _) hX₂
  rw [le_div_iff₀ (by positivity)]
  rw [mul_div_assoc', div_le_iff₀ (by positivity)] at this
  exact this.trans_eq (by ring)

public theorem BSG {K : ℝ} (hK : 0 ≤ K) (hB : B.Nonempty) (hAB : K⁻¹ * (#A ^ 2 * #B) ≤ E[A, B]) :
    ∃ A' ⊆ A, (2 ^ 4)⁻¹ * K⁻¹ * #A ≤ #A' ∧ #(A' - A') ≤ 2 ^ 10 * K ^ 5 * #B ^ 4 / #A ^ 3 := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · exact ⟨∅, by simp⟩
  obtain rfl | hK := eq_or_lt_of_le hK
  · exact ⟨∅, by simp⟩
  · obtain ⟨s, A', hA, h⟩ := BSG_aux hK (by simpa [card_pos]) (by simpa [card_pos]) hAB
    exact ⟨A', hA.trans (inter_subset_left ..), h⟩

public theorem BSG₂ {K : ℝ} (hK : 0 ≤ K) (hB : B.Nonempty) (hAB : K⁻¹ * (#A ^ 2 * #B) ≤ E[A, B]) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, (2 ^ 4)⁻¹ * K⁻¹ * #A ≤ #A' ∧
      (2 ^ 4)⁻¹ * K⁻¹ * #A ≤ #B' ∧ #(A' - B') ≤ 2 ^ 10 * K ^ 5 * #B ^ 4 / #A ^ 3 := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · exact ⟨∅, by simp, ∅, by simp⟩
  obtain rfl | hK := eq_or_lt_of_le hK
  · exact ⟨∅, by simp, ∅, by simp⟩
  · obtain ⟨s, A', hA, h⟩ := BSG_aux hK (by simpa [card_pos]) (by simpa [card_pos]) hAB
    refine ⟨A', hA.trans (inter_subset_left ..), -s +ᵥ A' ,?_, ?_⟩
    · calc
        -s +ᵥ A' ⊆ -s +ᵥ (A ∩ (s +ᵥ B)) := vadd_finset_subset_vadd_finset hA
        _ ⊆ -s +ᵥ (s +ᵥ B) := vadd_finset_subset_vadd_finset (inter_subset_right ..)
        _ = B := neg_vadd_vadd ..
    · refine ⟨h.1, (card_vadd_finset (-s) A') ▸ h.1, ?_⟩
      convert h.2 using 2
      simp only [sub_eq_add_neg, neg_vadd_finset_distrib, neg_neg]
      rw [add_vadd_comm]
      apply card_vadd_finset

public theorem BSG_self {K : ℝ} (hK : 0 ≤ K) (hA : A.Nonempty) (hAK : K⁻¹ * #A ^ 3 ≤ E[A]) :
    ∃ A' ⊆ A, (2 ^ 4)⁻¹ * K⁻¹ * #A ≤ #A' ∧ #(A' - A') ≤ 2 ^ 10 * K ^ 5 * #A := by
  convert BSG hK hA ?_ using 5
  · have := hA.card_pos
    field_simp
  · ring_nf
    assumption

public theorem BSG_self' {K : ℝ} (hK : 0 ≤ K) (hA : A.Nonempty) (hAK : K⁻¹ * #A ^ 3 ≤ E[A]) :
    ∃ A' ⊆ A, (2 ^ 4)⁻¹ * K⁻¹ * #A ≤ #A' ∧ #(A' - A') ≤ 2 ^ 14 * K ^ 6 * #A' := by
  obtain ⟨A', hA', hAA', hAK'⟩ := BSG_self hK hA hAK
  refine ⟨A', hA', hAA', hAK'.trans ?_⟩
  calc
    _ = 2 ^ 14 * K ^ 6 * ((2 ^ 4)⁻¹ * K⁻¹ * #A) := ?_
    _ ≤ _ := by gcongr
  obtain rfl | hK := hK.eq_or_lt
  · simp
  · field_simp

end lemma2
