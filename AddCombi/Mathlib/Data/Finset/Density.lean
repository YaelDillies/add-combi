module

public import Mathlib.Data.Finset.Density
public import Mathlib.Data.Fintype.Prod

public section

namespace Finset
variable {α β : Type*} [Fintype α] [Fintype β]

@[simp] lemma dens_product (s : Finset α) (t : Finset β) : (s ×ˢ t).dens = s.dens * t.dens := by
  simp [dens, mul_div_mul_comm]

end Finset
