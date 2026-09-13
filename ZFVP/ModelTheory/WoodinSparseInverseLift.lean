import ZFVP.ModelTheory.WoodinSparseThreadLift

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal θ]
local notation "N" => woodinNormalizedPrefixCode θ
local notation "C" => woodinNormalizedStageCode θ
local notation "Q" => woodinRecodingCarriers (woodinSparseRecodingHistory θ)
local notation "T" => woodinRecodingOrders (woodinSparseRecodingHistory θ)
local notation "m" => woodinRecodingMaps (woodinSparseRecodingHistory θ)
local notation "c" => forcingRecodedCode θ N Q T m
local notation "f" => woodinSparseInverseBaseMap θ c m

theorem woodinSparseStageMap_inverse_lift {i z p : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (ih : ∀ j ∈ θ, IsWoodinSparseLiftRow j) (hi : i ∈ θ)
    (hz : z ∈ (forcingCodeP C) ‘ θ) (hp : p ∈ (forcingCodeP C) ‘ i)
    (hle : ⟨p, ((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ) ‘ z⟩ₖ ∈ (forcingCodeR C) ‘ i) :
    (woodinSparseStageMap θ) ‘ (((forcingCodeL C) ‘ ⟨i, θ⟩ₖ) ‘ ⟨z, p⟩ₖ) =
      sparsePrefixReplace (succ (woodinSourceIndex i)) ((woodinSparseStageMap θ) ‘ z) ((woodinSparseStageMap i) ‘ p) := by
  let := hΩ.inaccessible.1
  let := IsOrdinal.of_mem hi
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hzero : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hlimit := ordinal_limit_of_not_successor hlim
  have rows := fun j hj ↦ woodinSparseRecodingRec_correct hΩ hAC j (hsub j hj)
  have hm := woodinSparseHistory_family hΩ hAC hsub rows
  have hT : ∀ j ∈ θ, IsForcingPreorder (Q ‘ j) (T ‘ j) := fun _ hj ↦ woodinSparseHistory_preorder rows hj
  have hQt := (woodinSparseRecodingHistory_tables θ).1
  have hTt := (woodinSparseRecodingHistory_tables θ).2.1
  have hsp : ∀ j ∈ θ, ∀ q ∈ Q ‘ j, IsSparseFunctionOn (succ (woodinSourceIndex j)) q :=
    fun _ hj _ hq ↦ woodinSparseHistory_sparse rows hj hq
  have hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ q ∈ Q ‘ j,
      ((forcingRecodedProjections θ N m) ‘ ⟨i, j⟩ₖ) ‘ q = q ↾ (succ (woodinSourceIndex i)) := by
    intro i hi j hj hij q hq
    let := IsOrdinal.of_mem hj
    exact woodinSparseHistory_projection hΩ hAC hsub rows hi hj (IsOrdinal.toIsTransitive.transitive _ hij) hq
  have ht : ∀ j ∈ θ, (forcingRecodedTops θ N m) ‘ j = ∅ := fun _ hj ↦ woodinSparseHistory_top hΩ hAC hsub rows hj
  have hd := (woodinNormalizedInverseCutoff_bounds hΩ hAC hθ h0 hlim hn).2.1
  have hQrank : ∀ j ∈ θ, Q ‘ j ∈ hierarchy (woodinNormalizedInverseCutoff θ) := by
    intro j hj
    apply woodinSparseHistory_small rows hj hd
    rw [woodinNormalizedInverseCutoff_actualCardinal hΩ hAC hsub h0 hlim hn]
    exact woodinIterationActualCardinal_increasing hΩ hAC hθ hj
  have hpN : p ∈ (forcingCodeP N) ‘ i := by
    rwa [(woodinNormalizedStage_old_carrier_order hΩ hAC hθ hi).1] at hp
  have hl := ((woodinNormalizedStageCode_valid hΩ hAC hθ).system.lifts.lift i
    (mem_succ_iff.mpr (Or.inr hi)) θ (mem_succ_self θ) (IsOrdinal.toIsTransitive.transitive _ hi) z hz p hp hle).1
  have hbase : kpair.π₁ z ∈ woodinNormalizedInverseBase θ := by
    have hz' := hz
    rw [(woodinNormalized_inverse_dictionary hΩ hAC hθ h0 hlim hn).1] at hz'
    obtain ⟨a, ha, τ, _, rfl⟩ := mem_prod_iff.mp hz'
    simpa only [kpair.π₁_kpair] using ha
  have hsplice : forcingThreadSplice θ (forcingCodeπ (woodinIterationPrefix θ))
      (forcingCodeL (woodinIterationPrefix θ)) (kpair.π₁ z) i p ∈ woodinNormalizedInverseBase θ := by
    have hl' := hl
    rw [woodinNormalizedStage_inverse_lift hΩ hAC hθ h0 hlim hn hi hz hpN,
      (woodinNormalized_inverse_dictionary hΩ hAC hθ h0 hlim hn).1] at hl'
    exact (kpair_mem_iff.mp hl').1
  have hS := (woodinIterationPrefix_of_stages
    (fun j hj ↦ ((woodinIterationExit hΩ hAC).2.1 j (hsub j hj)).1)).code
  have hM := woodinNormalizationHistory_actual_prefix hΩ hAC hsub
  have hv : ∀ j ∈ θ, (kpair.π₁ z) ‘ j ∈ (forcingCodeP N) ‘ j :=
    ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hbase).2.1
  have hpNorm : p ∈ (forcingNormalizationCarriers θ (woodinIterationPrefix θ)
      (woodinNormalizationHistory θ)) ‘ i := by
    simpa only [woodinNormalizedPrefixCode, forcingNormalizedCode, forcingCodeP_code] using hpN
  have hvNorm : ∀ j ∈ θ, (kpair.π₁ z) ‘ j ∈ (forcingNormalizationCarriers θ (woodinIterationPrefix θ)
      (woodinNormalizationHistory θ)) ‘ j := by
    simpa only [woodinNormalizedPrefixCode, forcingNormalizedCode, forcingCodeP_code] using hv
  have hnorm := forcingNormalized_threadSplice hS hM hi hpNorm hvNorm
  have hleN : ⟨p, (kpair.π₁ z) ‘ i⟩ₖ ∈ (forcingCodeR N) ‘ i := by
    rwa [woodinNormalizedStage_inverse_projection hΩ hAC hθ h0 hlim hn hi hz,
      (woodinNormalizedStage_old_carrier_order hΩ hAC hθ hi).2] at hle
  have hthread := woodinSparseThreadSplice_union hΩ hAC hsub ih hbase hi hpN hleN
  have hbaselift : f ‘ (forcingThreadSplice θ (forcingCodeπ (woodinIterationPrefix θ))
      (forcingCodeL (woodinIterationPrefix θ)) (kpair.π₁ z) i p) =
      sparsePrefixReplace (succ (woodinSourceIndex i)) (f ‘ (kpair.π₁ z)) ((woodinSparseStageMap i) ‘ p) := by
    rw [woodinSparseInverseBaseMap_value hΩ hAC hsub hm hT hQt hTt hzero hlimit hsp hπ hsplice,
      woodinSparseInverseBaseMap_value hΩ hAC hsub hm hT hQt hTt hzero hlimit hsp hπ hbase,
      ← hnorm]
    simpa only [woodinNormalizedPrefixCode, forcingNormalizedCode, forcingCodeπ_code, forcingCodeL_code] using hthread
  have hbs : IsSparseFunctionOn θ (f ‘ (kpair.π₁ z)) :=
    sparseThreadCarrier_isSparse (woodinSparseCompletedInverseMap_base_mem hΩ hAC hθ h0 hlim hn hm hT hQt hTt hsp hπ ht hQrank hz)
  have hpi : p ∈ (forcingCodeP (woodinNormalizedStageCode i)) ‘ i := by
    rwa [(woodinNormalizedPrefix_row hΩ hAC hsub hi).1] at hpN
  have hps := woodinSparseStageMap_sparse hΩ hAC (IsOrdinal.toIsTransitive.transitive _ (hsub i hi)) hpi
  have hb : succ (woodinSourceIndex i) ⊆ θ := by
    simpa only [woodinSparseBounds_value hi] using woodinSparseBounds_limit_subset hzero hlimit hi
  rw [woodinSparseStageMap_inverse h0 hlim hn]
  simp only [woodinSparsePrefixCode]
  rw [woodinSparseCompletedInverseMap_value hΩ hAC hθ h0 hlim hn hm hT hQt hTt hsp hπ ht hQrank hl,
    woodinSparseCompletedInverseMap_value hΩ hAC hθ h0 hlim hn hm hT hQt hTt hsp hπ ht hQrank hz,
    woodinNormalizedStage_inverse_lift hΩ hAC hθ h0 hlim hn hi hz hpN]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]
  rw [hbaselift, sparsePrefixReplace_append hbs hps hb]

end ZFVP
