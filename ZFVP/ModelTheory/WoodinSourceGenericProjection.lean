import ZFVP.ModelTheory.ForcingCanonicalTransport
import ZFVP.ModelTheory.WoodinSourceCompletedInverse
import ZFVP.ModelTheory.WoodinSourceLimitMaps
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSourceCode_inverse_generic_projection {θ s i : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (hi : i ∈ θ) {G : Set V}
    (hG : IsExternalForcingFilter (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s) G) :
    let θ' := woodinSourceIndex θ
    let s' := woodinSourceCode θ s
    let P := forcingInverseCodePoset θ s
    let P' := forcingInverseCodePoset θ' s'
    let G' := forcingProjectionGeneric P' (forcingInverseCodeOrder θ' s') (woodinSeedThreadMap θ P) G
    forcingProjectionGeneric ((forcingCodeP s') ‘ (woodinSourceIndex i))
      ((forcingCodeR s') ‘ (woodinSourceIndex i))
      ((forcingLimitProjectionColumn θ' P') ‘ (woodinSourceIndex i)) G' =
    forcingProjectionGeneric ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
      ((forcingLimitProjectionColumn θ P) ‘ i) G := by
  dsimp only
  let := IsOrdinal.of_mem hi
  have hzero : (∅ : V) ∈ θ := ordinal_mem_of_subset_mem (empty_subset i) hi
  have he := (woodinSourceCode_inverse_isomorphism hs).generic_projection_commutes
    (A := (forcingCodeP s) ‘ i) (T := (forcingCodeR s) ‘ i)
    (hs.system.inverseColumn hzero hs.subset_universe).order.preorder hG
    (fun p hp ↦ woodinSourceCode_inverse_projection hs hi hp)
  simpa only [woodinSourceCode, forcingCodeP_code, forcingCodeR_code,
    woodinInsertSeed_at_sourceIndex hi] using he

theorem woodinSourceCode_direct_generic_projection {θ s i : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (hi : i ∈ θ) {G : Set V}
    (hG : IsExternalForcingFilter ((forcingCodeP (forcingDirectCode θ s)) ‘ θ)
      ((forcingCodeR (forcingDirectCode θ s)) ‘ θ) G) :
    let θ' := woodinSourceIndex θ
    let s' := woodinSourceCode θ s
    let z := forcingDirectCode θ s
    let z' := forcingDirectCode θ' s'
    let P := (forcingCodeP z) ‘ θ
    let P' := (forcingCodeP z') ‘ θ'
    let G' := forcingProjectionGeneric P' ((forcingCodeR z') ‘ θ') (woodinSeedThreadMap θ P) G
    forcingProjectionGeneric ((forcingCodeP s') ‘ (woodinSourceIndex i))
      ((forcingCodeR s') ‘ (woodinSourceIndex i))
      ((forcingLimitProjectionColumn θ' P') ‘ (woodinSourceIndex i)) G' =
    forcingProjectionGeneric ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
      ((forcingLimitProjectionColumn θ P) ‘ i) G := by
  dsimp only
  let := IsOrdinal.of_mem hi
  have hzero : (∅ : V) ∈ θ := ordinal_mem_of_subset_mem (empty_subset i) hi
  have he := (woodinSourceCode_direct_isomorphism hs hzero).generic_projection_commutes
    (A := (forcingCodeP s) ‘ i) (T := (forcingCodeR s) ‘ i)
    ((forcingDirectCode_valid hs hzero).system.order.preorder θ (mem_succ_self θ)) hG
    (fun p hp ↦ woodinSourceCode_direct_projection hs hzero hi hp)
  simpa only [woodinSourceCode, forcingCodeP_code, forcingCodeR_code,
    woodinInsertSeed_at_sourceIndex hi] using he

theorem woodinSourceCode_completed_generic_projection {θ s i : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (hi : i ∈ θ) (γ : V)
    (hv : IsForcingIterationCode (succ θ)
      (forcingInverseSourceCollapseCode θ s (forcingInverseSourceCutoff θ s γ) γ)) {G : Set V}
    (hG : IsExternalForcingFilter
      ((forcingCodeP (forcingInverseSourceCollapseCode θ s (forcingInverseSourceCutoff θ s γ) γ)) ‘ θ)
      ((forcingCodeR (forcingInverseSourceCollapseCode θ s (forcingInverseSourceCutoff θ s γ) γ)) ‘ θ) G) :
    let θ' := woodinSourceIndex θ
    let s' := woodinSourceCode θ s
    let z := forcingInverseSourceCollapseCode θ s (forcingInverseSourceCutoff θ s γ) γ
    let z' := forcingInverseSourceCollapseCode θ' s' (forcingInverseSourceCutoff θ' s' γ) γ
    let G' := forcingProjectionGeneric ((forcingCodeP z') ‘ θ') ((forcingCodeR z') ‘ θ')
      (woodinSourceInverseCollapseMap θ s γ) G
    forcingProjectionGeneric ((forcingCodeP s') ‘ (woodinSourceIndex i))
      ((forcingCodeR s') ‘ (woodinSourceIndex i))
      ((forcingCodeπ z') ‘ ⟨woodinSourceIndex i, θ'⟩ₖ) G' =
    forcingProjectionGeneric ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
      ((forcingCodeπ z) ‘ ⟨i, θ⟩ₖ) G := by
  dsimp only
  let := IsOrdinal.of_mem hi
  have hzero : (∅ : V) ∈ θ := ordinal_mem_of_subset_mem (empty_subset i) hi
  have he := (woodinSourceCode_completed_inverse_isomorphism hs hzero γ).generic_projection_commutes
    (A := (forcingCodeP s) ‘ i) (T := (forcingCodeR s) ‘ i)
    (hv.system.order.preorder θ (mem_succ_self θ)) hG
    (fun p hp ↦ woodinSourceCode_completed_inverse_projection hs hzero hi γ hp)
  simpa only [woodinSourceCode, forcingCodeP_code, forcingCodeR_code,
    woodinInsertSeed_at_sourceIndex hi] using he
theorem woodinSourceCode_actual_completed_generic_projection {δ θ i : V} [IsOrdinal θ]
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) (hθ : θ ∈ δ)
    (hi : i ∈ θ) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    {G : Set V} (hG : IsExternalForcingFilter
      ((forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec θ))) ‘ θ) G) :
    let s := woodinIterationPrefix θ
    let K := woodinIterationCardinalPrefix θ
    let θ' := woodinSourceIndex θ
    let s' := woodinSourceCode θ s
    let z' := woodinInverseSourceCode θ' s' (woodinSourceCardinals θ K)
    let G' := forcingProjectionGeneric ((forcingCodeP z') ‘ θ') ((forcingCodeR z') ‘ θ')
      (woodinSourceInverseCollapseMap θ s (woodinLimitCardinal K)) G
    forcingProjectionGeneric ((forcingCodeP s') ‘ (woodinSourceIndex i))
      ((forcingCodeR s') ‘ (woodinSourceIndex i))
      ((forcingCodeπ z') ‘ ⟨woodinSourceIndex i, θ'⟩ₖ) G' =
    forcingProjectionGeneric ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
      ((forcingCodeπ (kpair.π₁ (woodinIterationRec θ))) ‘ ⟨i, θ⟩ₖ) G := by
  dsimp only
  let := hδ.inaccessible.1
  let := IsOrdinal.of_mem hi
  have hx := woodinIterationExit hδ hAC
  have hsub : θ ⊆ δ := IsOrdinal.toIsTransitive.transitive _ hθ
  have hs := (woodinIterationPrefix_of_stages (fun j hj ↦ (hx.2.1 j (hsub j hj)).1)).code
  have hn : θ ≠ ∅ := by rintro rfl; exact not_mem_empty hi
  have hz : (∅ : V) ∈ θ := ordinal_mem_of_subset_mem (empty_subset i) hi
  have hv := (hx.2.1 θ hθ).1.code
  rw [woodinIterationRec_inverse hn hlim hinac, kpair.π₁_kpair] at hv hG ⊢
  unfold woodinInverseSourceCode at hv hG ⊢
  rw [woodinSourceCardinals_actual_prefix_limit hδ hAC hsub hz]
  exact woodinSourceCode_completed_generic_projection hs hi _ hv hG
end ZFVP

