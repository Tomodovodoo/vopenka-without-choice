import ZFVP.ModelTheory.WoodinSparseInverseIsomorphism
import ZFVP.ModelTheory.WoodinRecodingCardinals

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ Q T m : V} [IsOrdinal θ]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
variable (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
variable (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
variable (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP (woodinNormalizedPrefixCode θ)) ‘ i)
  ((forcingCodeR (woodinNormalizedPrefixCode θ)) ‘ i) (Q ‘ i) (T ‘ i) (m ‘ i))
variable (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
variable (hQt : IsIterationTable θ Q) (hTt : IsIterationTable θ T)
variable (hsp : ∀ i ∈ θ, ∀ p ∈ Q ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p)
variable (hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ Q ‘ j,
  ((forcingRecodedProjections θ (woodinNormalizedPrefixCode θ) m) ‘ ⟨i, j⟩ₖ) ‘ p =
    p ↾ (succ (woodinSourceIndex i)))
variable (ht : ∀ i ∈ θ, (forcingRecodedTops θ (woodinNormalizedPrefixCode θ) m) ‘ i = ∅)
variable (hQrank : ∀ i ∈ θ, Q ‘ i ∈ hierarchy (woodinNormalizedInverseCutoff θ))

local notation "c" => forcingRecodedCode θ (woodinNormalizedPrefixCode θ) Q T m
local notation "δ" => woodinNormalizedInverseCutoff θ

include hΩ hAC hθ h0 hlim hn hm hT hQt hTt hsp hπ ht hQrank

theorem woodinSparseCompletedInverseCarrier_subset_hierarchy :
    woodinSparseCompletedInverseCarrier θ c ⊆ hierarchy δ := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hl := ordinal_limit_of_not_successor hlim
  have hc := forcingRecoded_code (woodinNormalizedPrefixCode_valid hΩ hAC hsub) hm hT hQt hTt
  have he := woodinSparseInverseCutoff_eq hΩ hAC hsub hm hT hQt hTt hz hl hsp hπ ht
  obtain ⟨_, hd, hθd, _⟩ := woodinNormalizedInverseCutoff_bounds hΩ hAC hθ h0 hlim hn
  let := hd.1
  have hA : woodinSparseInverseBase θ c ∈ hierarchy δ := by
    apply woodinSparseInverseBase_small hc hd (ordinal_mem_hierarchy_iff.mpr hθd)
    simpa only [forcingRecodedCode, forcingCodeP_code] using hQrank
  unfold woodinSparseCompletedInverseCarrier woodinSparseInversePool
  dsimp only
  rw [← he]
  exact sparsePairCarrier_subset_hierarchy hd.rankCriterion.2.2.1 (ordinal_mem_hierarchy_iff.mpr hθd)
    ((hierarchy_transitive δ).transitive _ hA) sep_subset

theorem woodinSparseCompletedInverseCarrier_small {ξ : V}
    (hξ : IsChoicelessInaccessible ξ) (hδξ : (kpair.π₂ (woodinIterationRec θ)) ‘ θ ∈ ξ) :
    woodinSparseCompletedInverseCarrier θ c ∈ hierarchy ξ := by
  let := hΩ.inaccessible.1
  let := hξ.1
  obtain ⟨_, hd, _, _⟩ := woodinNormalizedInverseCutoff_bounds hΩ hAC hθ h0 hlim hn
  let := hd.1
  apply subset_mem_hierarchy_limit hξ.rankCriterion.2.2.1 ?_
    (woodinSparseCompletedInverseCarrier_subset_hierarchy hΩ hAC hθ h0 hlim hn hm hT hQt hTt hsp hπ ht hQrank)
  rw [mem_hierarchy_iff_rank_mem, rank_hierarchy,
    woodinNormalizedInverseCutoff_actualCardinal hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hθ) h0 hlim hn]
  exact hδξ

end ZFVP
