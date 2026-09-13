import ZFVP.ModelTheory.TransitiveZFLimitColumns
import ZFVP.ModelTheory.InverseCollapseCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {ξ : V} [IsOrdinal ξ] [Nonempty (SetDomain (hierarchy ξ))]
  [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rank_forcingInverseCodePoset_val (hs : ∀ β ∈ ξ, succ β ∈ ξ)
    (θ s : SetDomain (hierarchy ξ)) :
    (forcingInverseCodePoset θ s).val = forcingInverseCodePoset θ.val s.val := by
  let := hierarchy_transitive ξ
  simp only [forcingInverseCodePoset, rank_forcingInverseLimit_val hs,
    TransitiveZF.forcingCodeP_val, TransitiveZF.forcingCodeπ_val, TransitiveZF.forcingCodeUniverse_val]

theorem rank_forcingInverseCodeOrder_val (hs : ∀ β ∈ ξ, succ β ∈ ξ)
    (θ s : SetDomain (hierarchy ξ)) :
    (forcingInverseCodeOrder θ s).val = forcingInverseCodeOrder θ.val s.val := by
  let := hierarchy_transitive ξ
  simp only [forcingInverseCodeOrder, TransitiveZF.forcingThreadOrder_val,
    TransitiveZF.forcingCodeR_val, rank_forcingInverseCodePoset_val hs]

theorem TransitiveZF.forcingInverseCodeTop_val (U : V) [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (θ s : SetDomain U) :
    (forcingInverseCodeTop θ s).val = forcingInverseCodeTop θ.val s.val := by
  simp only [forcingInverseCodeTop, forcingSectionThread_val U, forcingCodeπ_val U,
    forcingCodeE_val U, forcingCodet_val U, value_val_total U, empty_val U]

end ZFVP
