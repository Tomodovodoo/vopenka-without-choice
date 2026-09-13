import ZFVP.ModelTheory.WoodinSparseLiftRow

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω k : V} [IsOrdinal k]
local notation "C" => woodinNormalizedStageCode (succ k)
local notation "D" => woodinNormalizedStageCode k
local notation "Q" => woodinRecodingCarriers (woodinSparseRecodingHistory (succ k))
local notation "T" => woodinRecodingOrders (woodinSparseRecodingHistory (succ k))
local notation "m" => woodinRecodingMaps (woodinSparseRecodingHistory (succ k))
local notation "c" => woodinSparsePrefixCode (succ k)

theorem woodinSparseStageMap_successor_lift {i z p : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : succ k ∈ Ω)
    (ih : IsWoodinSparseLiftRow k) (hi : i ∈ succ k)
    (hz : z ∈ (forcingCodeP C) ‘ (succ k)) (hp : p ∈ (forcingCodeP C) ‘ i)
    (hle : ⟨p, ((forcingCodeπ C) ‘ ⟨i, succ k⟩ₖ) ‘ z⟩ₖ ∈ (forcingCodeR C) ‘ i) :
    (woodinSparseStageMap (succ k)) ‘ (((forcingCodeL C) ‘ ⟨i, succ k⟩ₖ) ‘ ⟨z, p⟩ₖ) =
      sparsePrefixReplace (succ (woodinSourceIndex i)) ((woodinSparseStageMap (succ k)) ‘ z)
        ((woodinSparseStageMap i) ‘ p) := by
  let := hΩ.inaccessible.1
  let := IsOrdinal.of_mem hi
  have hsub := IsOrdinal.toIsTransitive.transitive _ hk
  have hkΩ := hsub k (mem_succ_self k)
  have hksub := IsOrdinal.toIsTransitive.transitive _ hkΩ
  have rows := fun i hi ↦ woodinSparseRecodingRec_correct hΩ hAC i (hsub i hi)
  have hm := woodinSparseHistory_family hΩ hAC hsub rows
  have hT : ∀ i ∈ succ k, IsForcingPreorder (Q ‘ i) (T ‘ i) := fun _ hi ↦ woodinSparseHistory_preorder rows hi
  have hQt := (woodinSparseRecodingHistory_tables (succ k)).1
  have hTt := (woodinSparseRecodingHistory_tables (succ k)).2.1
  have hd := (woodinNormalizedSuccessorCutoff_bounds hΩ hAC hkΩ).1
  have hQrank : Q ‘ k ∈ hierarchy (woodinNormalizedSuccessorCutoff k) := by
    apply woodinSparseHistory_small rows (mem_succ_self k) hd
    rw [woodinNormalizedSuccessorCutoff_actualCardinal hΩ hAC hkΩ]
    exact woodinIterationActualCardinal_increasing hΩ hAC hk (mem_succ_self k)
  have hsp : ∀ p ∈ Q ‘ k, IsSparseFunctionOn (woodinSourceIndex (succ k)) p := by
    intro p hp
    rw [woodinSourceIndex_successor]
    exact woodinSparseHistory_sparse rows (mem_succ_self k) hp
  have hpD : p ∈ (forcingCodeP D) ‘ i := by
    rwa [woodinNormalizedStage_successor_old_carrier hΩ hAC hkΩ hi] at hp
  have hbase : kpair.π₁ z ∈ (forcingCodeP D) ‘ k := by
    have hz' := hz
    rw [(woodinNormalizedStage_successor_eq hΩ hAC hkΩ).1] at hz'
    obtain ⟨a, ha, τ, _, rfl⟩ := mem_prod_iff.mp hz'
    simpa only [kpair.π₁_kpair] using ha
  have hleD : ⟨p, ((forcingCodeπ D) ‘ ⟨i, k⟩ₖ) ‘ (kpair.π₁ z)⟩ₖ ∈ (forcingCodeR D) ‘ i := by
    rw [woodinNormalizedStage_successor_projection hΩ hAC hkΩ hi hz,
      (woodinNormalizedStage_old_carrier_order hΩ hAC hk hi).2,
      woodinNormalizedPrefix_successor hΩ hAC hkΩ] at hle
    exact hle
  have hold := ih i hi _ hbase p hpD hleD
  have hl := ((woodinNormalizedStageCode_valid hΩ hAC hk).system.lifts.lift i
    (mem_succ_iff.mpr (Or.inr hi)) (succ k) (mem_succ_self (succ k))
    (IsOrdinal.toIsTransitive.transitive _ hi) z hz p hp hle).1
  have hpi : p ∈ (forcingCodeP (woodinNormalizedStageCode i)) ‘ i := by
    rw [← woodinNormalizedPrefix_successor hΩ hAC hkΩ] at hpD
    rwa [(woodinNormalizedPrefix_row hΩ hAC hsub hi).1] at hpD
  have hbi := woodinSparseStageMap_sparse hΩ hAC (IsOrdinal.toIsTransitive.transitive _ (hsub i hi)) hpi
  have hps : IsSparseFunctionOn (woodinSourceIndex (succ k)) ((woodinSparseStageMap k) ‘ (kpair.π₁ z)) := by
    rw [woodinSourceIndex_successor]
    exact woodinSparseStageMap_sparse hΩ hAC hksub hbase
  have hbound : succ (woodinSourceIndex i) ⊆ woodinSourceIndex (succ k) := by
    rw [woodinSourceIndex_successor]
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact subset_refl _
    · simpa only [woodinSparseBounds_value (mem_succ_iff.mpr (Or.inr hi)), woodinSparseBounds_value (mem_succ_self k)] using
        woodinSparseBounds_mono hi (mem_succ_self k)
  rw [woodinSparseStageMap_successor]
  simp only [woodinSparsePrefixCode]
  change (woodinSparseSuccessorMap k (forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m) m) ‘ _ = _
  rw [woodinSparseSuccessorMap_value hΩ hAC hkΩ hm hT hQt hTt hQrank hsp hl,
    woodinSparseSuccessorMap_value hΩ hAC hkΩ hm hT hQt hTt hQrank hsp hz,
    woodinNormalizedStage_successor_lift hΩ hAC hkΩ hi hz hpD]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair, woodinSparseStageMap_history (mem_succ_self k)]
  rw [hold, sparsePrefixReplace_append hps hbi hbound]

end ZFVP
