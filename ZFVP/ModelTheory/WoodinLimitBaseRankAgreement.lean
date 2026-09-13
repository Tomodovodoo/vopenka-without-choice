import ZFVP.ModelTheory.TransitiveZFLimitColumns
import ZFVP.ModelTheory.TransitiveZFInaccessible

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rank_woodinLimitBase_val {ξ : V} [IsOrdinal ξ] [Nonempty (SetDomain (hierarchy ξ))]
    [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hs : ∀ β ∈ ξ, succ β ∈ ξ) (θ s K : SetDomain (hierarchy ξ)) :
    (woodinLimitBase θ s K).val = woodinLimitBase θ.val s.val K.val := by
  classical
  let := hierarchy_transitive ξ
  have he : IsChoicelessInaccessible (woodinLimitCardinal K) ↔
      IsChoicelessInaccessible (woodinLimitCardinal K.val) := by
    rw [rank_choicelessInaccessible_iff hs, TransitiveZF.woodinLimitCardinal_val]
  by_cases hi : IsChoicelessInaccessible (woodinLimitCardinal K)
  · rw [woodinLimitBase_direct hi, woodinLimitBase_direct (he.mp hi)]
    exact rank_forcingDirectCode_val hs θ s
  · rw [woodinLimitBase_inverse hi, woodinLimitBase_inverse (fun h ↦ hi (he.mpr h))]
    exact rank_forcingInverseCode_val hs θ s

end ZFVP
