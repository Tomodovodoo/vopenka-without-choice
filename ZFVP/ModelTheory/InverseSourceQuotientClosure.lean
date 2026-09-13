import ZFVP.ModelTheory.SaturatedHartogsQuotientClosureTransfer
import ZFVP.ModelTheory.InverseSourceCollapseCode
import ZFVP.ModelTheory.IterationQuotientClosure
import ZFVP.ModelTheory.InverseSplitProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem inverseSourceCollapseCode_quotient_closedBelow {θ s γ η i : V}
    [IsOrdinal θ] [IsOrdinal η]
    (hs : IsForcingIterationCode θ s) (h0 : ∅ ∈ θ) (hi : i ∈ θ)
    (hδ : IsChoicelessInaccessible (forcingInverseSourceCutoff θ s γ))
    (hP : forcingInverseCodePoset θ s ∈ hierarchy (forcingInverseSourceCutoff θ s γ))
    (hγδ : γ ∈ forcingInverseSourceCutoff θ s γ)
    (hκ : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        regularCardinalFormula (standardTuple ![forcingInverseHartogsName θ s γ]))
    (hηγ : η ⊆ γ)
    (hDC : ∀ p ∈ (forcingCodeP s) ‘ i,
      p ∈ forcingFormula ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
        dependentChoiceBelowFormula (standardTuple ![checkName ((forcingCodet s) ‘ i) η]))
    (hbase : IterationQuotientClosedBelow (forcingInverseCode θ s) i θ η) :
    IterationQuotientClosedBelow
      (forcingInverseSourceCollapseCode θ s (forcingInverseSourceCutoff θ s γ) γ) i θ η := by
  let c := forcingInverseSourceCutoff θ s γ
  let Q := saturatedHartogsPosetName (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
    (forcingInverseCodeTop θ s) γ c
  let S := saturatedHartogsOrderName (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
    (forcingInverseCodeTop θ s) γ c
  let z := forcingInverseTwoStepCode θ s Q S ∅
  have col := hs.system.inverseColumn h0 hs.subset_universe
  have hiter : IsForcingIterand (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s) Q S ∅ :=
    saturatedHartogsCollapse_iterand col.order.preorder col.tops.top hδ hκ
  have hz : IsForcingIterationCode (succ θ) z := forcingInverseTwoStepCode_valid hs h0 hiter
  have hi' : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
  have hPi : (forcingCodeP z) ‘ i = (forcingCodeP s) ‘ i := by
    simp only [z, forcingInverseTwoStepCode, forcingTwoStepColumnCode,
      forcingIterationCodeNext, forcingCodeP_code, forcingFamilyNext_old hi]
  have hRi : (forcingCodeR z) ‘ i = (forcingCodeR s) ‘ i := by
    simp only [z, forcingInverseTwoStepCode, forcingTwoStepColumnCode,
      forcingIterationCodeNext, forcingCodeR_code, forcingFamilyNext_old hi]
  have hti : (forcingCodet z) ‘ i = (forcingCodet s) ‘ i := by
    simp only [z, forcingInverseTwoStepCode, forcingTwoStepColumnCode,
      forcingIterationCodeNext, forcingCodet_code, forcingFamilyNext_old hi]
  have hτ := forcingInverseLimit_splitProjection hs.system.split hs.system.lifts hi hs.subset_universe
    (fun j hj k hk hjk ↦ hs.system.splitProjection hj hk hjk)
  have hproj := hz.system.projection hi' (mem_succ_self θ) (IsOrdinal.toIsTransitive.transitive _ hi)
  rw [hPi, hRi] at hproj
  change IterationQuotientClosedBelow z i θ η
  unfold IterationQuotientClosedBelow
  rw [hPi, hRi, hti]
  apply saturatedHartogs_quotient_closure_forced (hs.system.order.preorder i hi)
    (hs.system.tops.top i hi) hτ col.order.preorder col.tops.top hδ hP hγδ hκ
    (by simp only [Q, S, c, forcingInverseCodePoset, forcingInverseCodeOrder, forcingInverseCodeTop, z, forcingInverseTwoStepCode, forcingTwoStepColumnCode,
      forcingIterationCodeNext, forcingCodeP_code, forcingFamilyNext_new])
    (by simp only [Q, S, c, forcingInverseCodePoset, forcingInverseCodeOrder, forcingInverseCodeTop, z, forcingInverseTwoStepCode, forcingTwoStepColumnCode,
      forcingIterationCodeNext, forcingCodeR_code, forcingFamilyNext_new]) hproj ?_ hηγ hDC ?_
  · intro q hq
    have hq' : q ∈ twoStepConditions (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s) Q ∅ := by
      simpa only [forcingInverseCodePoset, forcingInverseCodeOrder, z, forcingInverseTwoStepCode, forcingTwoStepColumnCode,
        forcingIterationCodeNext, forcingCodeP_code, forcingFamilyNext_new] using hq
    simp only [z, forcingInverseTwoStepCode, forcingTwoStepColumnCode, forcingIterationCodeNext,
      forcingCodeπ_code, forcingMatrixNext_column hi, forcingComposeProjectionColumn_value hi,
      forcingLimitProjectionColumn_value hi]
    rw [value_compose_of_mem_function
      (twoStep_projection col.order.preorder col.tops.top hiter).maps hτ.projection.maps hq']
    exact congrArg (fun x ↦ (forcingThreadCoordinate (forcingInverseCodePoset θ s) i) ‘ x)
      (twoStepProjection_value hq').symm
  · simpa only [IterationQuotientClosedBelow, forcingInverseCode, forcingThreadCode,
      forcingIterationCodeNext, forcingCodeP_code, forcingCodeR_code, forcingCodet_code,
      forcingCodeπ_code, forcingFamilyNext_old hi, forcingFamilyNext_new,
      forcingMatrixNext_column hi, forcingLimitProjectionColumn_value hi] using hbase

end ZFVP
