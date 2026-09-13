import ZFVP.ModelTheory.WoodinSparseHistoryLaws
import ZFVP.ModelTheory.WoodinSparseDirectColumns
import ZFVP.ModelTheory.WoodinSparseDirectRank
import ZFVP.ModelTheory.WoodinSparseDirectTop

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

theorem woodinSparseRecodingDirectRow_correct
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (ih : ∀ i ∈ θ, IsWoodinSparseRow i (woodinSparseRecodingRec i)) :
    IsWoodinSparseRow θ (woodinSparseRecodingDirectRow θ c m) := by
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
  have ht : ∀ i ∈ θ, (forcingCodet c) ‘ i = ∅ := by
    simpa only [forcingRecodedCode, forcingCodet_code] using
      (fun i hi ↦ woodinSparseHistory_top hΩ hAC hsub ih (i := i) hi)
  have hc := forcingRecoded_code (woodinNormalizedPrefixCode_valid hΩ hAC hsub) hm hT hQt hTt
  have hsp' : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p := by
    simpa only [forcingRecodedCode, forcingCodeP_code] using hsp
  have hπ' : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
      ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)) := by
    simpa only [forcingRecodedCode, forcingCodeP_code, forcingCodeπ_code] using hπ
  have hE' : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ (forcingCodeP c) ‘ i,
      ((forcingCodeE c) ‘ ⟨i, j⟩ₖ) ‘ p = p := by
    simpa only [forcingRecodedCode, forcingCodeP_code, forcingCodeE_code] using hE
  have hf := woodinSparseDirectMap_isomorphism hΩ hAC hsub hm hT hQt hTt h0 hlim hsp hπ hE hinac
  simp only [IsWoodinSparseRow, IsWoodinRecodedRow, woodinSparseRecodingDirectRow,
    kpair.π₁_kpair, kpair.π₂_kpair]
  refine ⟨⟨hf, woodinSparseDirect_preorder hc hzero hl hsp' hπ' hE', ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro ξ hξ hcξ
    let := hξ.1
    have hcard := woodinDirect_stage_cardinal hΩ hAC hθ h0 hlim hinac
    have hs := woodinIterationPrefix_of_stages
      (fun i hi ↦ ((woodinIterationExit hΩ hAC).2.1 i (hsub i hi)).1)
    have he := hs.index_eq_regular_limit hl hinac.regular
    have hθinac : IsChoicelessInaccessible θ := he.symm ▸ hinac
    have hQθ : ∀ i ∈ θ, (forcingCodeP c) ‘ i ∈ hierarchy θ := by
      intro i hi
      simp only [forcingRecodedCode, forcingCodeP_code]
      apply woodinSparseHistory_small ih hi hθinac
      rw [← hcard]
      exact woodinIterationActualCardinal_increasing hΩ hAC hθ hi
    apply subset_mem_hierarchy_limit hξ.rankCriterion.2.2.1 ?_
      (woodinSparseDirectBase_subset_hierarchy_of_rows hc hQθ)
    rw [mem_hierarchy_iff_rank_mem, rank_hierarchy]
    exact hcard ▸ hcξ
  · intro p hp
    have hs := ((mem_woodinSparseInverseBase_iff hc).mp (mem_woodinSparseDirectBase_iff.mp hp).1).1
    refine ⟨hs.1, ?_, hs.2.2⟩
    rw [woodinSourceIndex_limit θ hzero hl]
    exact subset_trans hs.2.1 (fun x hx ↦ mem_succ_iff.mpr (Or.inr hx))
  · exact woodinSparseDirectMap_top hΩ hAC hsub hm hT hQt hTt h0 hlim hsp hπ hE hinac ht
  · intro i hi p hp
    rw [← (woodinSparseRecodingHistory_values hi).2.2]
    exact woodinSparseDirectMap_projection hΩ hAC hsub hm hT hQt hTt h0 hlim hsp hπ hE hinac hi hp
  · intro i hi p hp
    rw [(woodinNormalizedStage_old_carrier_order hΩ hAC hθ hi).1] at hp
    rw [← (woodinSparseRecodingHistory_values hi).2.2]
    exact woodinSparseDirectMap_section hΩ hAC hsub hm hT hQt hTt h0 hlim hsp hπ hE hinac hi hp

end ZFVP
