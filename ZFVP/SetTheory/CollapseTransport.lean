import ZFVP.SetTheory.CollapseDictionary
import ZFVP.SetTheory.UniformRank

/-! Elementary transport of the same collapse dictionary across models of ZF. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace ElementaryMap

variable {V W : Type*} [SetStructure V] [SetStructure W] [Nonempty V] [Nonempty W]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_internalWellFounded_iff (j : ElementaryMap V W) (R D : V) :
    IsInternallyWellFounded (j R) (j D) ↔ IsInternallyWellFounded R D :=
  (j.map_defined internallyWellFoundedFormula
    (fun v ↦ IsInternallyWellFounded (v 0) (v 1))
    (fun v ↦ IsInternallyWellFounded (v 0) (v 1)) ![R, D]).symm

theorem map_extensionalOn_iff (j : ElementaryMap V W) (R D : V) :
    IsExtensionalOn (j R) (j D) ↔ IsExtensionalOn R D :=
  (j.map_defined extensionalOnFormula (fun v ↦ IsExtensionalOn (v 0) (v 1))
    (fun v ↦ IsExtensionalOn (v 0) (v 1)) ![R, D]).symm

theorem map_mostowskiMap (j : ElementaryMap V W) (R D : V) :
    j (mostowskiMap R D) = mostowskiMap (j R) (j D) := by
  have h := j.map_defined mostowskiMapFormula (fun v ↦ v 0 = mostowskiMap (v 1) (v 2))
    (fun v ↦ v 0 = mostowskiMap (v 1) (v 2)) ![mostowskiMap R D, R, D]
  exact h.mp rfl

end ElementaryMap
end ZFVP
