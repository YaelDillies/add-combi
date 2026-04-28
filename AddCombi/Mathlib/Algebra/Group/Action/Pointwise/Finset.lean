module

public import AddCombi.Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Action.Pointwise.Finset

public section

open scoped Pointwise

namespace Finset
variable {G : Type*} [DecidableEq G] [Group G]

@[to_additive]
lemma card_inter_smul_eq_card_filter (s t : Finset G) (a : G) :
    #(s ∩ (a • t)) = #{x ∈ s ×ˢ t | x.1 / x.2 = a} := by
  rw [← card_smul_finset a⁻¹]
  refine card_nbij' (fun b ↦ (a * b, b)) Prod.snd ?_ ?_ ?_ ?_ <;>
    simp [Set.LeftInvOn, Set.MapsTo, eq_div_iff_mul_eq', eq_comm, Set.mem_inv_smul_set_iff]
  grind

@[to_additive]
lemma card_inter_smul_inv_eq_card_filter (s t : Finset G) (a : G) :
    #(s ∩ (a • t⁻¹)) = #{x ∈ s ×ˢ t | x.1 * x.2 = a} := by
  rw [← card_smul_finset a⁻¹]
  refine card_nbij' (fun b ↦ (a * b, b⁻¹)) (fun (x, y) ↦ y⁻¹) ?_ ?_ ?_ ?_ <;>
    simp [Set.LeftInvOn, Set.MapsTo, ← div_eq_iff_eq_mul, eq_comm, Set.mem_inv_smul_set_iff]
  grind [div_eq_mul_inv]

end Finset
