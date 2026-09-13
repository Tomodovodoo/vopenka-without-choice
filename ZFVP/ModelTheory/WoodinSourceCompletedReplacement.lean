import ZFVP.ModelTheory.WoodinSourceCompletedSections
import ZFVP.ModelTheory.WoodinSourceLimitReplacement
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
theorem forcingInverseSourceCollapseCode_replacement {θ s ζ γ i x b : V}
    (hi : i ∈ θ) (hb : b ∈ (forcingCodeP s) ‘ i)
    (hx : x ∈ (forcingCodeP (forcingInverseSourceCollapseCode θ s ζ γ)) ‘ θ) :
    ((forcingCodeL (forcingInverseSourceCollapseCode θ s ζ γ)) ‘ ⟨i, θ⟩ₖ) ‘ ⟨x, b⟩ₖ =
      ⟨forcingThreadSplice θ (forcingCodeπ s) (forcingCodeL s) (kpair.π₁ x) i b, kpair.π₂ x⟩ₖ := by
  have hx' := hx
  simp only [forcingInverseSourceCollapseCode, forcingInverseCollapseCode, forcingInverseTwoStepCode,
    forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeP_code, forcingFamilyNext_new] at hx'
  simp only [forcingInverseSourceCollapseCode, forcingInverseCollapseCode, forcingInverseTwoStepCode,
    forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeL_code, forcingMatrixNext_column hi]
  rw [forcingTwoStepLiftColumn_value hi hx' hb, successorForcingLiftValue, twoStepStronger,
    forcingLimitLiftColumn_value hi]
  have hf := forcingInverseSourceCollapseCode_first hx
  unfold forcingInverseCodePoset at hf
  rw [forcingLimitLift_value hf hb]



theorem woodinSourceInverseCollapseMap_value {θ s γ x : V}
    (hx : x ∈ (forcingCodeP (forcingInverseSourceCollapseCode θ s
      (forcingInverseSourceCutoff θ s γ) γ)) ‘ θ) :
    (woodinSourceInverseCollapseMap θ s γ) ‘ x =
      ⟨woodinInsertSeed θ (kpair.π₁ x) ∅,
        nameAction (woodinSeedThreadMap θ (forcingInverseCodePoset θ s)) (kpair.π₂ x)⟩ₖ := by
  have hf := forcingInverseSourceCollapseCode_first hx
  have hx' : x ∈ twoStepConditions (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseCollapseName θ s (forcingInverseSourceCutoff θ s γ)
        (forcingInverseHartogsName θ s γ) (forcingInverseRestorationName θ s γ)) ∅ := by
    simpa only [forcingInverseSourceCollapseCode, forcingInverseCollapseCode, forcingInverseTwoStepCode,
      forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeP_code, forcingFamilyNext_new,
      forcingInverseCodePoset, forcingInverseCodeOrder] using hx
  rw [woodinSourceInverseCollapseMap, twoStepIsomorphismMap, value_definableGraph _ _ _ hx']
  simp only [twoStepNameAction]
  rw [woodinSeedThreadMap, value_definableGraph _ _ _ hf]

theorem woodinSourceCode_completed_inverse_replacement {θ s i x b : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (hi : i ∈ θ) (hb : b ∈ (forcingCodeP s) ‘ i) (γ : V)
    (hx : x ∈ (forcingCodeP (forcingInverseSourceCollapseCode θ s
      (forcingInverseSourceCutoff θ s γ) γ)) ‘ θ)
    (hlift : ((forcingCodeL (forcingInverseSourceCollapseCode θ s
      (forcingInverseSourceCutoff θ s γ) γ)) ‘ ⟨i, θ⟩ₖ) ‘ ⟨x, b⟩ₖ ∈
        (forcingCodeP (forcingInverseSourceCollapseCode θ s
          (forcingInverseSourceCutoff θ s γ) γ)) ‘ θ) :
    let θ' := woodinSourceIndex θ
    let s' := woodinSourceCode θ s
    let z := forcingInverseSourceCollapseCode θ s (forcingInverseSourceCutoff θ s γ) γ
    let z' := forcingInverseSourceCollapseCode θ' s' (forcingInverseSourceCutoff θ' s' γ) γ
    (woodinSourceInverseCollapseMap θ s γ) ‘ (((forcingCodeL z) ‘ ⟨i, θ⟩ₖ) ‘ ⟨x, b⟩ₖ) =
      ((forcingCodeL z') ‘ ⟨woodinSourceIndex i, θ'⟩ₖ) ‘
        ⟨(woodinSourceInverseCollapseMap θ s γ) ‘ x, b⟩ₖ := by
  dsimp only
  let := IsOrdinal.of_mem hi
  have hz : (∅ : V) ∈ θ := ordinal_mem_of_subset_mem (empty_subset i) hi
  have hm := function_value_mem (woodinSourceCode_completed_inverse_isomorphism hs hz γ).1 hx
  have hb' : b ∈ (forcingCodeP (woodinSourceCode θ s)) ‘ (woodinSourceIndex i) := by
    simpa only [woodinSourceCode, forcingCodeP_code, woodinInsertSeed_at_sourceIndex hi] using hb
  rw [woodinSourceInverseCollapseMap_value hlift,
    forcingInverseSourceCollapseCode_replacement hi hb hx,
    forcingInverseSourceCollapseCode_replacement (woodinSourceIndex_mem_iff.mpr hi) hb' hm,
    woodinSourceInverseCollapseMap_value hx]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]
  rw [woodinSourceCode_threadSplice hi hb]


theorem woodinSourceCode_completed_inverse_replacement_of_valid {θ s i x b : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (hi : i ∈ θ) (hb : b ∈ (forcingCodeP s) ‘ i) (γ : V)
    (hx : x ∈ (forcingCodeP (forcingInverseSourceCollapseCode θ s
      (forcingInverseSourceCutoff θ s γ) γ)) ‘ θ)
    (hle : ⟨b, (kpair.π₁ x) ‘ i⟩ₖ ∈ (forcingCodeR s) ‘ i)
    (hv : IsForcingIterationCode (succ θ)
      (forcingInverseSourceCollapseCode θ s (forcingInverseSourceCutoff θ s γ) γ)) :
    let θ' := woodinSourceIndex θ
    let s' := woodinSourceCode θ s
    let z := forcingInverseSourceCollapseCode θ s (forcingInverseSourceCutoff θ s γ) γ
    let z' := forcingInverseSourceCollapseCode θ' s' (forcingInverseSourceCutoff θ' s' γ) γ
    (woodinSourceInverseCollapseMap θ s γ) ‘ (((forcingCodeL z) ‘ ⟨i, θ⟩ₖ) ‘ ⟨x, b⟩ₖ) =
      ((forcingCodeL z') ‘ ⟨woodinSourceIndex i, θ'⟩ₖ) ‘
        ⟨(woodinSourceInverseCollapseMap θ s γ) ‘ x, b⟩ₖ := by
  apply woodinSourceCode_completed_inverse_replacement hs hi hb γ hx
  have hb' : b ∈ (forcingCodeP (forcingInverseSourceCollapseCode θ s
      (forcingInverseSourceCutoff θ s γ) γ)) ‘ i := by
    simpa only [forcingInverseSourceCollapseCode, forcingInverseCollapseCode, forcingInverseTwoStepCode,
      forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeP_code, forcingFamilyNext_old hi] using hb
  have hle' : ⟨b, ((forcingCodeπ (forcingInverseSourceCollapseCode θ s
      (forcingInverseSourceCutoff θ s γ) γ)) ‘ ⟨i, θ⟩ₖ) ‘ x⟩ₖ ∈
        (forcingCodeR (forcingInverseSourceCollapseCode θ s
          (forcingInverseSourceCutoff θ s γ) γ)) ‘ i := by
    rw [forcingInverseSourceCollapseCode_projection hi hx]
    simpa only [forcingInverseSourceCollapseCode, forcingInverseCollapseCode, forcingInverseTwoStepCode,
      forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeR_code, forcingFamilyNext_old hi] using hle
  exact (hv.system.lifts.lift i (mem_succ_iff.mpr (Or.inr hi)) θ (mem_succ_self θ)
    (IsOrdinal.toIsTransitive.transitive _ hi) x hx b hb' hle').1


theorem woodinSourceCode_actual_completed_inverse_replacement {δ θ i x b : V} [IsOrdinal θ]
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) (hθ : θ ∈ δ)
    (hi : i ∈ θ) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hb : b ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i)
    (hx : x ∈ (forcingCodeP (woodinInverseSourceCode θ (woodinIterationPrefix θ)
      (woodinIterationCardinalPrefix θ))) ‘ θ)
    (hle : ⟨b, (kpair.π₁ x) ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i) :
    let s := woodinIterationPrefix θ
    let K := woodinIterationCardinalPrefix θ
    let z := woodinInverseSourceCode θ s K
    let z' := woodinInverseSourceCode (woodinSourceIndex θ)
      (woodinSourceCode θ s) (woodinSourceCardinals θ K)
    (woodinSourceInverseCollapseMap θ s (woodinLimitCardinal K)) ‘
        (((forcingCodeL z) ‘ ⟨i, θ⟩ₖ) ‘ ⟨x, b⟩ₖ) =
      ((forcingCodeL z') ‘ ⟨woodinSourceIndex i, woodinSourceIndex θ⟩ₖ) ‘
        ⟨(woodinSourceInverseCollapseMap θ s (woodinLimitCardinal K)) ‘ x, b⟩ₖ := by
  dsimp only
  let := hδ.inaccessible.1
  let := IsOrdinal.of_mem hi
  have hexit := woodinIterationExit hδ hAC
  have hsub : θ ⊆ δ := IsOrdinal.toIsTransitive.transitive _ hθ
  have hs := (woodinIterationPrefix_of_stages (fun j hj ↦ (hexit.2.1 j (hsub j hj)).1)).code
  have hn : θ ≠ ∅ := by rintro rfl; exact not_mem_empty hi
  have hz : (∅ : V) ∈ θ := ordinal_mem_of_subset_mem (empty_subset i) hi
  have hv := (hexit.2.1 θ hθ).1.code
  rw [woodinIterationRec_inverse hn hlim hinac, kpair.π₁_kpair] at hv
  unfold woodinInverseSourceCode at hv hx ⊢
  rw [woodinSourceCardinals_actual_prefix_limit hδ hAC hsub hz]
  exact woodinSourceCode_completed_inverse_replacement_of_valid hs hi hb _ hx hle hv
end ZFVP
