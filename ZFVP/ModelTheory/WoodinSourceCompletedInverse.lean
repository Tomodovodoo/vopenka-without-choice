import ZFVP.ModelTheory.ForcingIsomorphismCanonicalTwoStep
import ZFVP.ModelTheory.WoodinSourceCardinalLimit

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSourceInverseCollapseMap (θ s γ : V) : V :=
  twoStepIsomorphismMap (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
    (forcingInverseCollapseName θ s (forcingInverseSourceCutoff θ s γ)
      (forcingInverseHartogsName θ s γ) (forcingInverseRestorationName θ s γ)) ∅
    (woodinSeedThreadMap θ (forcingInverseCodePoset θ s))

theorem forcingInverseSourceCollapseCode_first {θ s ζ γ x : V}
    (hx : x ∈ (forcingCodeP (forcingInverseSourceCollapseCode θ s ζ γ)) ‘ θ) :
    kpair.π₁ x ∈ forcingInverseCodePoset θ s := by
  simp only [forcingInverseSourceCollapseCode, forcingInverseCollapseCode, forcingInverseTwoStepCode,
    forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeP_code, forcingFamilyNext_new] at hx
  simpa only [twoStepProjection_value hx, forcingInverseCodePoset] using
    function_value_mem (twoStepProjection_maps _ _ _ _) hx

theorem forcingInverseSourceCollapseCode_projection {θ s ζ γ i x : V} (hi : i ∈ θ)
    (hx : x ∈ (forcingCodeP (forcingInverseSourceCollapseCode θ s ζ γ)) ‘ θ) :
    ((forcingCodeπ (forcingInverseSourceCollapseCode θ s ζ γ)) ‘ ⟨i, θ⟩ₖ) ‘ x =
      (kpair.π₁ x) ‘ i := by
  have hx' := hx
  simp only [forcingInverseSourceCollapseCode, forcingInverseCollapseCode, forcingInverseTwoStepCode,
    forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeP_code, forcingFamilyNext_new] at hx'
  simp only [forcingInverseSourceCollapseCode, forcingInverseCollapseCode, forcingInverseTwoStepCode,
    forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeπ_code,
    forcingMatrixNext_column hi, forcingComposeProjectionColumn_value hi, forcingLimitProjectionColumn_value hi]
  rw [value_compose_of_mem_function (twoStepProjection_maps _ _ _ _) (forcingThreadCoordinate_maps hi) hx',
    twoStepProjection_value hx']
  exact forcingThreadCoordinate_value (forcingInverseSourceCollapseCode_first hx)

theorem woodinSourceCode_completed_inverse_isomorphism {θ s : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (hzero : (∅ : V) ∈ θ) (γ : V) :
    let c := forcingInverseSourceCutoff θ s γ
    let s' := woodinSourceCode θ s
    let θ' := woodinSourceIndex θ
    let c' := forcingInverseSourceCutoff θ' s' γ
    let z := forcingInverseSourceCollapseCode θ s c γ
    let z' := forcingInverseSourceCollapseCode θ' s' c' γ
    IsForcingIsomorphism ((forcingCodeP z) ‘ θ) ((forcingCodeR z) ‘ θ)
      ((forcingCodeP z') ‘ θ') ((forcingCodeR z') ‘ θ')
      (woodinSourceInverseCollapseMap θ s γ) := by
  dsimp only
  have hc := hs.system.inverseColumn hzero hs.subset_universe
  have hz : (∅ : V) ∈ woodinSourceIndex θ :=
    subset_ordinalAdd 1 θ ∅ (by change (0 : V) ∈ succ 0; simp)
  have hs' := woodinSourceCode_valid hs
  have hc' := hs'.system.inverseColumn hz hs'.subset_universe
  have he := saturatedHartogsCollapse_isomorphism (ζ := forcingInverseSourceCutoff θ s γ)
    hc.order.preorder hc'.order.preorder (woodinSourceCode_inverse_isomorphism hs)
    hc.tops.top hc'.tops.top (woodinSourceCode_inverse_top_value hs hzero)
    γ (forcingInverseSourceCutoff θ s γ)
  dsimp only at he
  rw [← woodinSourceCode_inverse_cutoff hs hzero γ]
  simpa only [forcingInverseSourceCollapseCode, forcingInverseCollapseCode,
    forcingInverseTwoStepCode, forcingTwoStepColumnCode, forcingIterationCodeNext,
    forcingCodeP_code, forcingCodeR_code, forcingFamilyNext_new,
    forcingInverseCollapseName, forcingInverseHartogsName, forcingInverseRestorationName,
    forcingInverseCodePoset, forcingInverseCodeOrder, forcingInverseCodeTop,
    woodinSourceInverseCollapseMap, ← woodinSourceCode_inverse_cutoff hs hzero γ] using he

theorem woodinSourceCode_actual_completed_inverse {δ θ : V} [IsOrdinal θ]
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V)
    (hθ : θ ⊆ δ) (hzero : (∅ : V) ∈ θ) :
    let s := woodinIterationPrefix θ
    let K := woodinIterationCardinalPrefix θ
    let z := woodinInverseSourceCode θ s K
    let z' := woodinInverseSourceCode (woodinSourceIndex θ)
      (woodinSourceCode θ s) (woodinSourceCardinals θ K)
    IsForcingIsomorphism ((forcingCodeP z) ‘ θ) ((forcingCodeR z) ‘ θ)
      ((forcingCodeP z') ‘ (woodinSourceIndex θ)) ((forcingCodeR z') ‘ (woodinSourceIndex θ))
      (woodinSourceInverseCollapseMap θ s (woodinLimitCardinal K)) := by
  dsimp only
  have hx := woodinIterationExit hδ hAC
  have hi := woodinIterationPrefix_of_stages (fun i hi ↦ (hx.2.1 i (hθ i hi)).1)
  have he := woodinSourceCode_completed_inverse_isomorphism hi.code hzero
    (woodinLimitCardinal (woodinIterationCardinalPrefix θ))
  unfold woodinInverseSourceCode
  rw [woodinSourceCardinals_actual_prefix_limit hδ hAC hθ hzero]
  exact he

theorem woodinSourceCode_completed_inverse_projection {θ s i x : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (hzero : (∅ : V) ∈ θ) (hi : i ∈ θ) (γ : V)
    (hx : x ∈ (forcingCodeP (forcingInverseSourceCollapseCode θ s
      (forcingInverseSourceCutoff θ s γ) γ)) ‘ θ) :
    let θ' := woodinSourceIndex θ
    let s' := woodinSourceCode θ s
    let z := forcingInverseSourceCollapseCode θ s (forcingInverseSourceCutoff θ s γ) γ
    let z' := forcingInverseSourceCollapseCode θ' s' (forcingInverseSourceCutoff θ' s' γ) γ
    ((forcingCodeπ z') ‘ ⟨woodinSourceIndex i, θ'⟩ₖ) ‘ ((woodinSourceInverseCollapseMap θ s γ) ‘ x) =
      ((forcingCodeπ z) ‘ ⟨i, θ⟩ₖ) ‘ x := by
  dsimp only
  let := IsOrdinal.of_mem hi
  have hm := function_value_mem (woodinSourceCode_completed_inverse_isomorphism hs hzero γ).1 hx
  rw [forcingInverseSourceCollapseCode_projection (woodinSourceIndex_mem_iff.mpr hi) hm,
    forcingInverseSourceCollapseCode_projection hi hx]
  have hp := forcingInverseSourceCollapseCode_first hx
  have hx' : x ∈ twoStepConditions (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseCollapseName θ s (forcingInverseSourceCutoff θ s γ)
        (forcingInverseHartogsName θ s γ) (forcingInverseRestorationName θ s γ)) ∅ := by
    simpa only [forcingInverseSourceCollapseCode, forcingInverseCollapseCode, forcingInverseTwoStepCode,
      forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeP_code, forcingFamilyNext_new,
      forcingInverseCodePoset, forcingInverseCodeOrder] using hx
  rw [woodinSourceInverseCollapseMap, twoStepIsomorphismMap, value_definableGraph _ _ _ hx']
  simp only [twoStepNameAction, kpair.π₁_kpair]
  rw [woodinSeedThreadMap, value_definableGraph _ _ _ hp, woodinInsertSeed_at_sourceIndex hi]

end ZFVP
