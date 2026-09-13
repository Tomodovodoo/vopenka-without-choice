import ZFVP.ModelTheory.WoodinSparseInverseStage
import ZFVP.ModelTheory.WoodinSparseInverseTop

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ Q T m : V} [IsOrdinal θ]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
variable (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP (woodinNormalizedPrefixCode θ)) ‘ i)
  ((forcingCodeR (woodinNormalizedPrefixCode θ)) ‘ i) (Q ‘ i) (T ‘ i) (m ‘ i))
variable (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
variable (hQt : IsIterationTable θ Q) (hTt : IsIterationTable θ T)
variable (h0 : ∅ ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ)
variable (hsp : ∀ i ∈ θ, ∀ p ∈ Q ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p)
variable (hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ Q ‘ j,
  ((forcingRecodedProjections θ (woodinNormalizedPrefixCode θ) m) ‘ ⟨i, j⟩ₖ) ‘ p =
    p ↾ (succ (woodinSourceIndex i)))
variable (ht : ∀ i ∈ θ, (forcingRecodedTops θ (woodinNormalizedPrefixCode θ) m) ‘ i = ∅)

local notation "c" => forcingRecodedCode θ (woodinNormalizedPrefixCode θ) Q T m

include hΩ hAC hθ hm hT hQt hTt h0 hlim hsp hπ ht

theorem woodinSparseInverseBase_recoded_laws :
    IsForcingPreorder (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c) ∧
      IsForcingTop (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c) ∅ := by
  have hc := forcingRecoded_code (woodinNormalizedPrefixCode_valid hΩ hAC hθ) hm hT hQt hTt
  have hsp' : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p := by
    simpa only [forcingRecodedCode, forcingCodeP_code] using hsp
  have hπ' : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
      ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)) := by
    simpa only [forcingRecodedCode, forcingCodeP_code, forcingCodeπ_code] using hπ
  have ht' : ∀ i ∈ θ, (forcingCodet c) ‘ i = ∅ := by
    simpa only [forcingRecodedCode, forcingCodet_code] using ht
  exact ⟨woodinSparseInverse_preorder hc h0 hlim hsp' hπ', woodinSparseInverse_empty_top hc h0 hlim hsp' hπ' ht'⟩

theorem woodinSparseInverseBaseMap_top :
    (woodinSparseInverseBaseMap θ c m) ‘ (forcingInverseCodeTop θ (woodinIterationPrefix θ)) = ∅ := by
  have hc := forcingRecoded_code (woodinNormalizedPrefixCode_valid hΩ hAC hθ) hm hT hQt hTt
  have hf := woodinRecodedInverseBaseMap_isomorphism (Q := Q) (T := T) (m := m) hΩ hAC hθ hm hT hQt hTt
  have he := woodinSparseInverseFlatten_recoded_isomorphism hΩ hAC hθ hm hT hQt hTt h0 hlim hsp hπ
  have hsource := (woodinNormalized_inverse_base_laws hΩ hAC hθ h0).2
  rw [woodinSparseInverseBaseMap, value_compose_of_mem_function hf.1 he.1 hsource.1,
    woodinRecodedInverseBaseMap_top hΩ hAC hθ hm hT hQt hTt h0]
  apply woodinSparseInverseFlatten_top hc h0
  · simpa only [forcingRecodedCode, forcingCodeP_code] using hsp
  · simpa only [forcingRecodedCode, forcingCodeP_code, forcingCodeπ_code] using hπ
  · simpa only [forcingRecodedCode, forcingCodet_code] using ht

theorem woodinSparseInverseCutoff_eq : woodinNormalizedInverseCutoff θ = woodinSparseInverseCutoff θ c := by
  have hf := woodinSparseInverseBaseMap_isomorphism hΩ hAC hθ hm hT hQt hTt h0 hlim hsp hπ
  have hs := woodinNormalized_inverse_base_laws hΩ hAC hθ h0
  have htgt := woodinSparseInverseBase_recoded_laws hΩ hAC hθ hm hT hQt hTt h0 hlim hsp hπ ht
  exact hf.hartogs_prefix_cutoff hs.1 htgt.1 hs.2 htgt.2
    (woodinSparseInverseBaseMap_top hΩ hAC hθ hm hT hQt hTt h0 hlim hsp hπ ht)
    (woodinLimitCardinal (woodinIterationCardinalPrefix θ))

omit hθ h0 hlim in
theorem woodinSparseInversePairMap_isomorphism
    (hθΩ : θ ∈ Ω) (hz : θ ≠ ∅) (hl : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hQrank : ∀ i ∈ θ, Q ‘ i ∈ hierarchy (woodinNormalizedInverseCutoff θ)) :
    IsForcingIsomorphism ((forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ)
      ((forcingCodeR (woodinNormalizedStageCode θ)) ‘ θ)
      (woodinSparseInversePairCarrier θ c) (woodinSparseInversePairOrder θ c) (woodinSparseInversePairMap θ c m) := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθΩ
  have hzero : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ hz he.symm)
  have hlimit := ordinal_limit_of_not_successor hl
  have hc := forcingRecoded_code (woodinNormalizedPrefixCode_valid hΩ hAC hsub) hm hT hQt hTt
  have hf := woodinSparseInverseBaseMap_isomorphism hΩ hAC hsub hm hT hQt hTt hzero hlimit hsp hπ
  have hs := woodinNormalized_inverse_base_laws hΩ hAC hsub hzero
  have htgt := woodinSparseInverseBase_recoded_laws hΩ hAC hsub hm hT hQt hTt hzero hlimit hsp hπ ht
  have htop := woodinSparseInverseBaseMap_top hΩ hAC hsub hm hT hQt hTt hzero hlimit hsp hπ ht
  obtain ⟨_, hd, hθd, hP⟩ := woodinNormalizedInverseCutoff_bounds hΩ hAC hθΩ hz hl hn
  let := hd.1
  have hA : woodinSparseInverseBase θ c ∈ hierarchy (woodinNormalizedInverseCutoff θ) := by
    apply woodinSparseInverseBase_small hc hd (ordinal_mem_hierarchy_iff.mpr hθd)
    simpa only [forcingRecodedCode, forcingCodeP_code] using hQrank
  obtain ⟨hp, hr⟩ := woodinNormalized_inverse_dictionary hΩ hAC hθΩ hz hl hn
  rw [hp, hr]
  exact normalizedHartogsSuccessor_isomorphism hf hs.1 htgt.1 hs.2 htgt.2 htop hd hP hA

omit hθ h0 hlim in
theorem woodinSparseCompletedInverseMap_isomorphism
    (hθΩ : θ ∈ Ω) (hz : θ ≠ ∅) (hl : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hQrank : ∀ i ∈ θ, Q ‘ i ∈ hierarchy (woodinNormalizedInverseCutoff θ)) :
    IsForcingIsomorphism ((forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ)
      ((forcingCodeR (woodinNormalizedStageCode θ)) ‘ θ)
      (woodinSparseCompletedInverseCarrier θ c) (woodinSparseCompletedInverseOrder θ c)
      (woodinSparseCompletedInverseMap θ c m) := by
  have hf := woodinSparseInversePairMap_isomorphism hΩ hAC hm hT hQt hTt hsp hπ ht hθΩ hz hl hn hQrank
  exact hf.comp woodinSparseInverseEncode_isomorphism

end ZFVP
