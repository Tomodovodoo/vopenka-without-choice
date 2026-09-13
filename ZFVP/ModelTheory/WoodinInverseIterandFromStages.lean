import ZFVP.ModelTheory.WoodinInverseFirstCoordinates
import ZFVP.ModelTheory.TwoStepIterandFromTop

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinInverse_iterand_of_stages {δ θ j : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) (hj : j ∈ θ) (h0 : j ≠ ∅)
    (hlim : j ≠ succ (⋃ˢ j))
    (hinac : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j))) :
    let s := woodinIterationPrefix j
    let γ := woodinLimitCardinal (woodinIterationCardinalPrefix j)
    let Q := forcingInverseCollapseName j s (forcingInverseSourceCutoff j s γ)
      (forcingInverseHartogsName j s γ) (forcingInverseRestorationName j s γ)
    IsForcingIterand (forcingInverseCodePoset j s) (forcingInverseCodeOrder j s) Q
      (reverseInclusionOrderName (forcingInverseCodePoset j s) (forcingInverseCodeOrder j s) Q) ∅ := by
  let := IsOrdinal.of_mem hj
  have h0j : (∅ : V) ∈ j := (IsOrdinal.subset_iff.mp (empty_subset j)).resolve_left
    (fun he ↦ h0 he.symm)
  have hlocal := (woodinIterationPrefix_of_stages
    (fun k hk ↦ hs k (IsOrdinal.toIsTransitive.mem_trans hk hj))).code
  have col := hlocal.system.inverseColumn h0j hlocal.subset_universe
  apply reverseInclusion_empty_iterand_of_top_pair col.order.preorder col.tops.top
    (forcingSaturatedName_isName _ _ _ _)
  have ht := ((hs j hj).code.system.tops.top j (mem_succ_self j)).1
  rw [woodinIterationRec_inverse h0 hlim hinac, kpair.π₁_kpair] at ht
  simpa only [woodinInverseSourceCode, forcingInverseSourceCollapseCode, forcingInverseCollapseCode,
    forcingInverseTwoStepCode, forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodet_code,
    forcingCodeP_code, forcingFamilyNext_new, forcingInverseCodePoset, forcingInverseCodeOrder,
    forcingInverseCodeTop, forcingInverseCollapseName, saturatedWoodinCollapseName] using ht

end ZFVP
