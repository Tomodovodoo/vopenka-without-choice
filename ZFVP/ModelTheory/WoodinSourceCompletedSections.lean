import ZFVP.ModelTheory.WoodinSourceLimitMaps
import ZFVP.ModelTheory.WoodinSourceCompletedInverse

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingInverseSourceCollapseCode_section {θ s ζ γ i p : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (hi : i ∈ θ) (hp : p ∈ (forcingCodeP s) ‘ i) :
    ((forcingCodeE (forcingInverseSourceCollapseCode θ s ζ γ)) ‘ ⟨i, θ⟩ₖ) ‘ p =
      ⟨forcingSectionThread θ (forcingCodeπ s) (forcingCodeE s) i p, ∅⟩ₖ := by
  let := IsOrdinal.of_mem hi
  have hz : (∅ : V) ∈ θ := ordinal_mem_of_subset_mem (empty_subset i) hi
  have col := hs.system.inverseColumn hz hs.subset_universe
  have hF := col.functions.sectionMap i hi
  rw [forcingLimitSectionColumn_value hi] at hF
  let C := forcingInverseCodePoset θ s
  have he : twoStepSection C (∅ : V) ∈ (C ×ˢ {∅}) ^ C := by
    apply definableGraph_mem_function_of_mapsTo
    intro x hx
    exact kpair_mem_iff.mpr ⟨hx, by simp⟩
  have hH : forcingSectionThread θ (forcingCodeπ s) (forcingCodeE s) i p ∈ C := by
    simpa only [C, forcingInverseCodePoset, forcingThreadSection_value hp] using function_value_mem hF hp
  simp only [forcingInverseSourceCollapseCode, forcingInverseCollapseCode,
    forcingInverseTwoStepCode, forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeE_code,
    forcingMatrixNext_column hi, forcingComposeSectionColumn_value hi, forcingLimitSectionColumn_value hi]
  dsimp only [C, forcingInverseCodePoset] at he hH
  rw [value_compose_of_mem_function hF he hp, forcingThreadSection_value hp]
  exact twoStepSection_value hH

theorem woodinSourceCode_completed_inverse_section {θ s i p : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (hi : i ∈ θ) (hp : p ∈ (forcingCodeP s) ‘ i) (γ : V)
    (hsection : ⟨forcingSectionThread θ (forcingCodeπ s) (forcingCodeE s) i p, ∅⟩ₖ ∈
      (forcingCodeP (forcingInverseSourceCollapseCode θ s (forcingInverseSourceCutoff θ s γ) γ)) ‘ θ) :
    let θ' := woodinSourceIndex θ
    let s' := woodinSourceCode θ s
    let z := forcingInverseSourceCollapseCode θ s (forcingInverseSourceCutoff θ s γ) γ
    let z' := forcingInverseSourceCollapseCode θ' s' (forcingInverseSourceCutoff θ' s' γ) γ
    (woodinSourceInverseCollapseMap θ s γ) ‘ (((forcingCodeE z) ‘ ⟨i, θ⟩ₖ) ‘ p) =
      ((forcingCodeE z') ‘ ⟨woodinSourceIndex i, θ'⟩ₖ) ‘ p := by
  dsimp only
  let := IsOrdinal.of_mem hi
  have hp' : p ∈ (forcingCodeP (woodinSourceCode θ s)) ‘ (woodinSourceIndex i) := by
    simpa only [woodinSourceCode, forcingCodeP_code, woodinInsertSeed_at_sourceIndex hi] using hp
  rw [forcingInverseSourceCollapseCode_section hs hi hp,
    forcingInverseSourceCollapseCode_section (woodinSourceCode_valid hs)
      (woodinSourceIndex_mem_iff.mpr hi) hp']
  have hm : forcingSectionThread θ (forcingCodeπ s) (forcingCodeE s) i p ∈ forcingInverseCodePoset θ s :=
    forcingDirectLimit_subset _ _ _ _ _ _ (forcingSectionThread_mem hs.system.split hi hp hs.subset_universe)
  have hx : ⟨forcingSectionThread θ (forcingCodeπ s) (forcingCodeE s) i p, ∅⟩ₖ ∈
      twoStepConditions (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        (forcingInverseCollapseName θ s (forcingInverseSourceCutoff θ s γ)
          (forcingInverseHartogsName θ s γ) (forcingInverseRestorationName θ s γ)) ∅ := by
    simpa only [forcingInverseSourceCollapseCode, forcingInverseCollapseCode, forcingInverseTwoStepCode,
      forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeP_code, forcingFamilyNext_new,
      forcingInverseCodePoset, forcingInverseCodeOrder] using hsection
  rw [woodinSourceInverseCollapseMap, twoStepIsomorphismMap, value_definableGraph _ _ _ hx]
  simp only [twoStepNameAction, kpair.π₁_kpair, kpair.π₂_kpair, nameAction_empty]
  rw [woodinSeedThreadMap, value_definableGraph _ _ _ hm, woodinSourceCode_sectionThread hi hp]

theorem woodinSourceCode_completed_inverse_section_of_valid {θ s i p : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (hi : i ∈ θ) (hp : p ∈ (forcingCodeP s) ‘ i) (γ : V)
    (hv : IsForcingIterationCode (succ θ)
      (forcingInverseSourceCollapseCode θ s (forcingInverseSourceCutoff θ s γ) γ)) :
    let θ' := woodinSourceIndex θ
    let s' := woodinSourceCode θ s
    let z := forcingInverseSourceCollapseCode θ s (forcingInverseSourceCutoff θ s γ) γ
    let z' := forcingInverseSourceCollapseCode θ' s' (forcingInverseSourceCutoff θ' s' γ) γ
    (woodinSourceInverseCollapseMap θ s γ) ‘ (((forcingCodeE z) ‘ ⟨i, θ⟩ₖ) ‘ p) =
      ((forcingCodeE z') ‘ ⟨woodinSourceIndex i, θ'⟩ₖ) ‘ p := by
  apply woodinSourceCode_completed_inverse_section hs hi hp γ
  have hp' : p ∈ (forcingCodeP (forcingInverseSourceCollapseCode θ s
      (forcingInverseSourceCutoff θ s γ) γ)) ‘ i := by
    simpa only [forcingInverseSourceCollapseCode, forcingInverseCollapseCode, forcingInverseTwoStepCode,
      forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeP_code, forcingFamilyNext_old hi] using hp
  have hm := hv.system.split.secMaps i (mem_succ_iff.mpr (Or.inr hi)) θ (mem_succ_self θ)
    (IsOrdinal.toIsTransitive.transitive _ hi) p hp'
  rwa [forcingInverseSourceCollapseCode_section hs hi hp] at hm

theorem woodinSourceCode_actual_completed_inverse_section {δ θ i p : V} [IsOrdinal θ]
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) (hθ : θ ∈ δ)
    (hi : i ∈ θ) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hp : p ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i) :
    let s := woodinIterationPrefix θ
    let K := woodinIterationCardinalPrefix θ
    let z := woodinInverseSourceCode θ s K
    let z' := woodinInverseSourceCode (woodinSourceIndex θ)
      (woodinSourceCode θ s) (woodinSourceCardinals θ K)
    (woodinSourceInverseCollapseMap θ s (woodinLimitCardinal K)) ‘
        (((forcingCodeE z) ‘ ⟨i, θ⟩ₖ) ‘ p) =
      ((forcingCodeE z') ‘ ⟨woodinSourceIndex i, woodinSourceIndex θ⟩ₖ) ‘ p := by
  dsimp only
  let := hδ.inaccessible.1
  let := IsOrdinal.of_mem hi
  have hx := woodinIterationExit hδ hAC
  have hsub : θ ⊆ δ := IsOrdinal.toIsTransitive.transitive _ hθ
  have hs := (woodinIterationPrefix_of_stages (fun j hj ↦ (hx.2.1 j (hsub j hj)).1)).code
  have hn : θ ≠ ∅ := by rintro rfl; exact not_mem_empty hi
  have hz : (∅ : V) ∈ θ := ordinal_mem_of_subset_mem (empty_subset i) hi
  have hv := (hx.2.1 θ hθ).1.code
  rw [woodinIterationRec_inverse hn hlim hinac, kpair.π₁_kpair] at hv
  unfold woodinInverseSourceCode at hv ⊢
  rw [woodinSourceCardinals_actual_prefix_limit hδ hAC hsub hz]
  exact woodinSourceCode_completed_inverse_section_of_valid hs hi hp _ hv

end ZFVP
