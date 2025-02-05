import AddCombi.DiscreteAnalysis.Convolution.Defs
import Mathlib.Algebra.Order.Star.Conjneg

open Finset Function Real
open scoped ComplexConjugate NNReal Pointwise

variable {G R : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

section OrderedCommSemiring
variable [OrderedCommSemiring R] {f g : G → R}

lemma conv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ∗ g :=
  fun _a ↦ sum_nonneg fun _x _ ↦ mul_nonneg (hf _) (hg _)

variable [StarRing R] [StarOrderedRing R]

lemma diffConv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ○ g :=
  fun _a ↦ sum_nonneg fun _x _ ↦ mul_nonneg (hf _) $ star_nonneg_iff.2 $ hg _

end OrderedCommSemiring

section StrictOrderedCommSemiring
variable [StrictOrderedCommSemiring R] {f g : G → R}

--TODO: Those can probably be generalised to `OrderedCommSemiring` but we don't really care
@[simp] lemma support_conv (hf : 0 ≤ f) (hg : 0 ≤ g) : support (f ∗ g) = support f + support g := by
  refine (support_conv_subset _ _).antisymm ?_
  rintro _ ⟨a, ha, b, hb, rfl⟩
  rw [mem_support, conv_apply_add]
  exact ne_of_gt $ sum_pos' (fun c _ ↦ mul_nonneg (hf _) $ hg _) ⟨0, mem_univ _,
    mul_pos ((hf _).lt_of_ne' $ by simpa using ha) $ (hg _).lt_of_ne' $ by simpa using hb⟩

lemma conv_pos (hf : 0 < f) (hg : 0 < g) : 0 < f ∗ g := by
  rw [Pi.lt_def] at hf hg ⊢
  obtain ⟨hf, a, ha⟩ := hf
  obtain ⟨hg, b, hb⟩ := hg
  refine ⟨conv_nonneg hf hg, a + b, ?_⟩
  rw [conv_apply_add]
  exact sum_pos' (fun c _ ↦ mul_nonneg (hf _) $ hg _) ⟨0, by simpa using mul_pos ha hb⟩

variable [StarRing R] [StarOrderedRing R]

@[simp]
lemma support_diffConv (hf : 0 ≤ f) (hg : 0 ≤ g) : support (f ○ g) = support f - support g := by
  simpa [sub_eq_add_neg] using support_conv hf (conjneg_nonneg.2 hg)

lemma diffConv_pos (hf : 0 < f) (hg : 0 < g) : 0 < f ○ g := by
  rw [← conv_conjneg]; exact conv_pos hf (conjneg_pos.2 hg)

end StrictOrderedCommSemiring

section OrderedCommSemiring
variable [OrderedCommSemiring R] {f g : G → R} {n : ℕ}

@[simp] lemma iterConv_nonneg (hf : 0 ≤ f) : ∀ {n}, 0 ≤ f ∗^ n
  | 0 => fun _ ↦ by dsimp; split_ifs <;> norm_num
  | n + 1 => conv_nonneg (iterConv_nonneg hf) hf

end OrderedCommSemiring

section StrictOrderedCommSemiring
variable [StrictOrderedCommSemiring R] [StarRing R] [StarOrderedRing R] {f g : G → R} {n : ℕ}

@[simp] lemma iterConv_pos (hf : 0 < f) : ∀ {n}, 0 < f ∗^ n
  | 0 => Pi.lt_def.2 ⟨iterConv_nonneg hf.le, 0, by simp⟩
  | n + 1 => conv_pos (iterConv_pos hf) hf

end StrictOrderedCommSemiring

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

section
variable [OrderedCommSemiring R] {f g : G → R}

private lemma conv_nonneg_of_pos_of_nonneg (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ f ∗ g :=
  conv_nonneg hf.le hg

private lemma conv_nonneg_of_nonneg_of_pos (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ f ∗ g :=
  conv_nonneg hf hg.le

variable [StarRing R] [StarOrderedRing R]

private lemma diffConv_nonneg_of_pos_of_nonneg (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ f ○ g :=
  diffConv_nonneg hf.le hg

private lemma diffConv_nonneg_of_nonneg_of_pos (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ f ○ g :=
  diffConv_nonneg hf hg.le

end

-- TODO: `^positivity` extension
