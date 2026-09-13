import ZFVP.ModelTheory.TransitiveZFTwoStepColumns
import ZFVP.ModelTheory.RankInverseCodeParameters
import ZFVP.ModelTheory.InverseTwoStepCode
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rank_forcingInverseTwoStepCode_val {ξ : V} [IsOrdinal ξ]
    [Nonempty (SetDomain (hierarchy ξ))] [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hclosed : ∀ β ∈ ξ, succ β ∈ ξ) (θ s Q S u : SetDomain (hierarchy ξ))
    (hR : IsForcingPreorder (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s))
    (hQ : IsForcingName (forcingInverseCodePoset θ s) Q)
    (hS : IsForcingName (forcingInverseCodePoset θ s) S)
    (hu : IsForcingName (forcingInverseCodePoset θ s) u) :
    (forcingInverseTwoStepCode θ s Q S u).val =
      forcingInverseTwoStepCode θ.val s.val Q.val S.val u.val := by
  let := hierarchy_transitive ξ
  simp only [forcingInverseCodePoset, forcingInverseCodeOrder] at hR hQ hS hu
  unfold forcingInverseTwoStepCode
  dsimp only
  rw [TransitiveZF.forcingTwoStepColumnCode_val (hierarchy ξ) θ s _ _ _ _ _ _ Q S u hR hQ hS hu]
  simp only [rank_forcingInverseLimit_val hclosed, TransitiveZF.forcingThreadOrder_val,
    TransitiveZF.forcingCodeP_val, TransitiveZF.forcingCodeR_val, TransitiveZF.forcingCodeπ_val,
    TransitiveZF.forcingCodeE_val, TransitiveZF.forcingCodeL_val, TransitiveZF.forcingCodet_val,
    TransitiveZF.forcingCodeUniverse_val, TransitiveZF.forcingLimitProjectionColumn_val,
    TransitiveZF.forcingLimitSectionColumn_val, TransitiveZF.forcingLimitLiftColumn_val,
    TransitiveZF.forcingSectionThread_val, TransitiveZF.value_val_total, TransitiveZF.empty_val]

theorem forcingInverseTwoStepCode_order_congr {θ s Q S T u : V}
    (h : twoStepOrder (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s) Q S u =
      twoStepOrder (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s) Q T u) :
    forcingInverseTwoStepCode θ s Q S u = forcingInverseTwoStepCode θ s Q T u := by
  unfold forcingInverseTwoStepCode forcingTwoStepColumnCode
  change forcingIterationCodeNext θ s _ (twoStepOrder (forcingInverseCodePoset θ s)
      (forcingInverseCodeOrder θ s) Q S u) _ _ _ _ = _
  rw [h]
  rfl
end ZFVP


