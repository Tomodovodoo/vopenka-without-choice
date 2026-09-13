import ZFVP.ModelTheory.WoodinSparseHistoryLaws
import ZFVP.ModelTheory.WoodinSparseInverseColumns
import ZFVP.ModelTheory.WoodinSparseInverseRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal θ]
local notation "Q" => woodinRecodingCarriers (woodinSparseRecodingHistory θ)
local notation "T" => woodinRecodingOrders (woodinSparseRecodingHistory θ)
local notation "m" => woodinRecodingMaps (woodinSparseRecodingHistory θ)
local notation "N" => woodinNormalizedPrefixCode θ
local notation "C" => woodinNormalizedStageCode θ
local notation "c" => forcingRecodedCode θ N Q T m

theorem woodinSparseRecodingInverseRow_correct
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (ih : ∀ i ∈ θ, IsWoodinSparseRow i (woodinSparseRecodingRec i)) :
    IsWoodinSparseRow θ (woodinSparseRecodingInverseRow θ c m) := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hzero : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hl := ordinal_limit_of_not_successor hlim
  have hm := woodinSparseHistory_family hΩ hAC hsub ih
  have hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i) := fun _ hi ↦ woodinSparseHistory_preorder ih hi
  have hQt := (woodinSparseRecodingHistory_tables θ).1
  have hTt := (woodinSparseRecodingHistory_tables θ).2.1
  have hsp : ∀ i ∈ θ, ∀ p ∈ Q ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p :=
    fun _ hi _ hp ↦ woodinSparseHistory_sparse ih hi hp
  have hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ Q ‘ j,
      ((forcingRecodedProjections θ N m) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)) := by
    intro i hi j hj hij p hp
    let := IsOrdinal.of_mem hj
    exact woodinSparseHistory_projection hΩ hAC hsub ih hi hj (IsOrdinal.toIsTransitive.transitive _ hij) hp
  have hE : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ Q ‘ i,
      ((forcingRecodedSections θ N m) ‘ ⟨i, j⟩ₖ) ‘ p = p :=
    fun _ hi _ hj hij _ hp ↦ woodinSparseHistory_section hΩ hAC hsub ih hi hj hij hp
  have ht : ∀ i ∈ θ, (forcingRecodedTops θ N m) ‘ i = ∅ :=
    fun _ hi ↦ woodinSparseHistory_top hΩ hAC hsub ih hi
  obtain ⟨_, hd, _, _⟩ := woodinNormalizedInverseCutoff_bounds hΩ hAC hθ h0 hlim hn
  have hQrank : ∀ i ∈ θ, Q ‘ i ∈ hierarchy (woodinNormalizedInverseCutoff θ) := by
    intro i hi
    apply woodinSparseHistory_small ih hi hd
    rw [woodinNormalizedInverseCutoff_actualCardinal hΩ hAC hsub h0 hlim hn]
    exact woodinIterationActualCardinal_increasing hΩ hAC hθ hi
  have hf := woodinSparseCompletedInverseMap_isomorphism hΩ hAC hm hT hQt hTt hsp hπ ht hθ h0 hlim hn hQrank
  have hs := woodinNormalizedStageCode_valid hΩ hAC hθ
  simp only [IsWoodinSparseRow, IsWoodinRecodedRow, woodinSparseRecodingInverseRow,
    kpair.π₁_kpair, kpair.π₂_kpair]
  refine ⟨⟨hf, hf.target_preorder (hs.system.order.preorder θ (mem_succ_self θ))
    (forcingPullbackOrder_subset _ _ _), ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro ξ hξ hcξ
    exact woodinSparseCompletedInverseCarrier_small hΩ hAC hθ h0 hlim hn hm hT hQt hTt hsp hπ ht hQrank hξ hcξ
  · intro p hp
    rw [woodinSourceIndex_limit θ hzero hl]
    exact (mem_sparsePairCarrier_iff.mp hp).1
  · exact woodinSparseCompletedInverseMap_top hΩ hAC hθ h0 hlim hn hm hT hQt hTt hsp hπ ht hQrank
  · intro i hi p hp
    rw [← (woodinSparseRecodingHistory_values hi).2.2]
    exact woodinSparseCompletedInverseMap_projection hΩ hAC hθ h0 hlim hn hm hT hQt hTt hsp hπ ht hQrank hi hp
  · intro i hi p hp
    rw [(woodinNormalizedStage_old_carrier_order hΩ hAC hθ hi).1] at hp
    rw [← (woodinSparseRecodingHistory_values hi).2.2]
    exact woodinSparseCompletedInverseMap_section hΩ hAC hθ h0 hlim hn hm hT hQt hTt hsp hπ ht hQrank hi hp hE

end ZFVP
