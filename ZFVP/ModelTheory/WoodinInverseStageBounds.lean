import ZFVP.ModelTheory.WoodinInverseSourceStage
import ZFVP.SetTheory.TwoStepRankBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinInverseCardinalNext (θ s K : V) : V :=
  forcingFamilyNext θ K (forcingInverseSourceCutoff θ s (woodinLimitCardinal K))

noncomputable def woodinInverseSourceCode (θ s K : V) : V :=
  forcingInverseSourceCollapseCode θ s (forcingInverseSourceCutoff θ s (woodinLimitCardinal K))
    (woodinLimitCardinal K)

theorem woodinInverseSourceCode_old {θ s K i : V} (hi : i ∈ θ) :
    woodinIterationStage (woodinInverseSourceCode θ s K) (woodinInverseCardinalNext θ s K) i =
      woodinIterationStage s K i := by
  simp only [woodinIterationStage, woodinInverseSourceCode, forcingInverseSourceCollapseCode,
    forcingInverseCollapseCode, forcingInverseTwoStepCode, forcingTwoStepColumnCode,
    forcingIterationCodeNext, forcingCodeP_code, forcingCodeR_code, forcingCodet_code,
    woodinInverseCardinalNext, forcingFamilyNext_old hi]

theorem saturatedWoodinCollapseName_mem_hierarchy {P R ζ κ ν ε : V}
    (hε : IsChoicelessInaccessible ε) (hP : P ∈ hierarchy ε) (hζ : ζ ∈ ε) :
    saturatedWoodinCollapseName P R ζ κ ν ∈ hierarchy ε := by
  let := hε.1
  exact subset_mem_hierarchy_limit hε.rankCriterion.2.2.1
    (prod_mem_hierarchy_limit hε.rankCriterion.2.2.1 (forcingNameHierarchy_mem_hierarchy hε hP hζ) hP)
    (forcingSaturatedName_subset _ _ _ _)

theorem IsWoodinIteration.inverse_sourceStage_small {δ θ s K : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hc : woodinLimitCardinal K ∈ forcingInverseSourceCutoff θ s (woodinLimitCardinal K)) :
    IsWoodinStageSmall (woodinIterationStage (woodinInverseSourceCode θ s K)
      (woodinInverseCardinalNext θ s K) θ) := by
  intro ε hε hb
  have he : forcingInverseSourceCutoff θ s (woodinLimitCardinal K) ∈ ε := by
    simpa only [woodinIterationStage, woodinStageCardinal_code, woodinInverseCardinalNext,
      forcingFamilyNext_new] using hb
  let := hε.1
  have hγε := IsOrdinal.toIsTransitive.mem_trans hc he
  have hs := h.inverse_small_above_limit hlim hε hγε
  have hQ := saturatedWoodinCollapseName_mem_hierarchy (R := forcingInverseCodeOrder θ s)
    (κ := forcingInverseHartogsName θ s (woodinLimitCardinal K))
    (ν := forcingInverseRestorationName θ s (woodinLimitCardinal K)) hε hs.1 he
  have hz : (∅ : V) ∈ hierarchy ε := ordinal_mem_hierarchy_iff.mpr (hε.regular.2.1 ∅ (by simp))
  have hh := twoStepConditions_mem_hierarchy_limit (R := forcingInverseCodeOrder θ s)
    hε.rankCriterion.2.2.1 hs.1 hQ hz
  simpa only [woodinIterationStage, woodinStagePoset_code, woodinInverseSourceCode,
    forcingInverseSourceCollapseCode, forcingInverseCollapseCode, forcingInverseTwoStepCode,
    forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeP_code, forcingFamilyNext_new,
    forcingInverseCollapseName, forcingInverseCodePoset, forcingInverseCodeOrder] using hh

end ZFVP
