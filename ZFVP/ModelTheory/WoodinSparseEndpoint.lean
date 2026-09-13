import ZFVP.ModelTheory.WoodinSparseConstruction
import ZFVP.ModelTheory.WoodinNormalizedEndpoint

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω : V}
local notation "Q" => woodinRecodingCarriers (woodinSparseRecodingHistory Ω)
local notation "T" => woodinRecodingOrders (woodinSparseRecodingHistory Ω)
local notation "m" => woodinRecodingMaps (woodinSparseRecodingHistory Ω)
local notation "N" => woodinNormalizedPrefixCode Ω
local notation "C" => woodinNormalizedStageCode Ω
local notation "c" => forcingRecodedCode Ω N Q T m

theorem woodinSparseRecodingRec_endpoint_correct
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    IsWoodinSparseRow Ω (woodinSparseRecodingRec Ω) := by
  let := hΩ.inaccessible.1
  obtain ⟨h0, hlim, hinac⟩ := woodinEndpoint_branch hΩ hAC
  have ih := woodinSparseRecodingRec_correct hΩ hAC
  have hsub : Ω ⊆ Ω := subset_refl Ω
  have hzero : (∅ : V) ∈ Ω := (IsOrdinal.subset_iff.mp (empty_subset Ω)).resolve_left (fun he ↦ h0 he.symm)
  have hl := ordinal_limit_of_not_successor hlim
  have hm := woodinSparseHistory_family hΩ hAC hsub ih
  have hT : ∀ i ∈ Ω, IsForcingPreorder (Q ‘ i) (T ‘ i) := fun _ hi ↦ woodinSparseHistory_preorder ih hi
  have hQt := (woodinSparseRecodingHistory_tables Ω).1
  have hTt := (woodinSparseRecodingHistory_tables Ω).2.1
  have hsp : ∀ i ∈ Ω, ∀ p ∈ Q ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p :=
    fun _ hi _ hp ↦ woodinSparseHistory_sparse ih hi hp
  have hπ : ∀ i ∈ Ω, ∀ j ∈ Ω, i ∈ j → ∀ p ∈ Q ‘ j,
      ((forcingRecodedProjections Ω N m) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)) := by
    intro i hi j hj hij p hp
    let := IsOrdinal.of_mem hj
    exact woodinSparseHistory_projection hΩ hAC hsub ih hi hj (IsOrdinal.toIsTransitive.transitive _ hij) hp
  have hE : ∀ i ∈ Ω, ∀ j ∈ Ω, i ⊆ j → ∀ p ∈ Q ‘ i,
      ((forcingRecodedSections Ω N m) ‘ ⟨i, j⟩ₖ) ‘ p = p :=
    fun _ hi _ hj hij _ hp ↦ woodinSparseHistory_section hΩ hAC hsub ih hi hj hij hp
  have ht : ∀ i ∈ Ω, (forcingCodet c) ‘ i = ∅ := by
    simpa only [forcingRecodedCode, forcingCodet_code] using
      (fun i hi ↦ woodinSparseHistory_top hΩ hAC hsub ih (i := i) hi)
  have hc := forcingRecoded_code (woodinNormalizedPrefixCode_valid hΩ hAC hsub) hm hT hQt hTt
  have hsp' : ∀ i ∈ Ω, ∀ p ∈ (forcingCodeP c) ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p := by
    simpa only [forcingRecodedCode, forcingCodeP_code] using hsp
  have hπ' : ∀ i ∈ Ω, ∀ j ∈ Ω, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
      ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)) := by
    simpa only [forcingRecodedCode, forcingCodeP_code, forcingCodeπ_code] using hπ
  have hE' : ∀ i ∈ Ω, ∀ j ∈ Ω, i ⊆ j → ∀ p ∈ (forcingCodeP c) ‘ i,
      ((forcingCodeE c) ‘ ⟨i, j⟩ₖ) ‘ p = p := by
    simpa only [forcingRecodedCode, forcingCodeP_code, forcingCodeE_code] using hE
  have hf := woodinSparseDirectMap_isomorphism hΩ hAC hsub hm hT hQt hTt h0 hlim hsp hπ hE hinac
  rw [woodinSparseRecodingRec_rule]
  change IsWoodinSparseRow Ω (woodinSparseRecodingRowRule Ω c m)
  simp only [woodinSparseRecodingRowRule, ite_eq_right h0, ite_eq_right hlim, ite_eq_left hinac,
    IsWoodinSparseRow, IsWoodinRecodedRow, woodinSparseRecodingDirectRow,
    kpair.π₁_kpair, kpair.π₂_kpair]
  refine ⟨⟨hf, woodinSparseDirect_preorder hc hzero hl hsp' hπ' hE', ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro ξ hξ hcξ
    let := hξ.1
    have hcard := woodinIteration_endpoint_cardinal hΩ hAC
    have hQΩ : ∀ i ∈ Ω, (forcingCodeP c) ‘ i ∈ hierarchy Ω := by
      intro i hi
      simp only [forcingRecodedCode, forcingCodeP_code]
      apply woodinSparseHistory_small ih hi hΩ.inaccessible
      exact ((woodinIterationExit hΩ hAC).2.1 i hi).1.bounded i (mem_succ_self i)
    apply subset_mem_hierarchy_limit hξ.rankCriterion.2.2.1 ?_
      (woodinSparseDirectBase_subset_hierarchy_of_rows hc hQΩ)
    rw [mem_hierarchy_iff_rank_mem, rank_hierarchy]
    exact hcard ▸ hcξ
  · intro p hp
    have hs := ((mem_woodinSparseInverseBase_iff hc).mp (mem_woodinSparseDirectBase_iff.mp hp).1).1
    refine ⟨hs.1, ?_, hs.2.2⟩
    rw [woodinSourceIndex_limit Ω hzero hl]
    exact subset_trans hs.2.1 (fun x hx ↦ mem_succ_iff.mpr (Or.inr hx))
  · exact woodinSparseDirectMap_top hΩ hAC hsub hm hT hQt hTt h0 hlim hsp hπ hE hinac ht
  · intro i hi p hp
    rw [← (woodinSparseRecodingHistory_values hi).2.2]
    exact woodinSparseDirectMap_projection hΩ hAC hsub hm hT hQt hTt h0 hlim hsp hπ hE hinac hi hp
  · intro i hi p hp
    have he := (woodinNormalizedPrefixCode_valid hΩ hAC hsub).tableP.value_of_subset
      (woodinNormalizedStageCode_endpoint_valid hΩ hAC).tableP
      (woodinNormalizedStageCode_endpoint_extends hΩ hAC).subP hi
    rw [← he] at hp
    rw [← (woodinSparseRecodingHistory_values hi).2.2]
    exact woodinSparseDirectMap_section hΩ hAC hsub hm hT hQt hTt h0 hlim hsp hπ hE hinac hi hp

end ZFVP

