import ZFVP.ModelTheory.ForcingNormalizationLimits
import ZFVP.ModelTheory.TransitiveZFLimitColumns

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingThreadAction_val (θ m f : SetDomain U) :
    (forcingThreadAction θ m f).val = forcingThreadAction θ.val m.val f.val := by
  unfold forcingThreadAction
  apply definableGraph_val U
  intro i _
  rw [value_val_total U, value_val_total U, value_val_total U]

theorem forcingThreadActionMap_val (θ m C : SetDomain U) :
    (forcingThreadActionMap θ m C).val = forcingThreadActionMap θ.val m.val C.val := by
  unfold forcingThreadActionMap
  apply definableGraph_val U
  intro f _
  exact forcingThreadAction_val U θ m f

end TransitiveZF

variable {ξ : V} [IsOrdinal ξ] [Nonempty (SetDomain (hierarchy ξ))]
  [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rank_forcingNormalizationDirectMap_val (hs : ∀ β ∈ ξ, succ β ∈ ξ)
    (θ s m : SetDomain (hierarchy ξ)) :
    (forcingNormalizationDirectMap θ s m).val = forcingNormalizationDirectMap θ.val s.val m.val := by
  let := hierarchy_transitive ξ
  unfold forcingNormalizationDirectMap
  rw [TransitiveZF.forcingThreadActionMap_val, TransitiveZF.value_val_total,
    TransitiveZF.forcingCodeP_val, rank_forcingDirectCode_val hs]

theorem rank_forcingNormalizationInverseMap_val (hs : ∀ β ∈ ξ, succ β ∈ ξ)
    (θ s m : SetDomain (hierarchy ξ)) :
    (forcingNormalizationInverseMap θ s m).val = forcingNormalizationInverseMap θ.val s.val m.val := by
  let := hierarchy_transitive ξ
  unfold forcingNormalizationInverseMap
  rw [TransitiveZF.forcingThreadActionMap_val, TransitiveZF.value_val_total,
    TransitiveZF.forcingCodeP_val, rank_forcingInverseCode_val hs]

end ZFVP
