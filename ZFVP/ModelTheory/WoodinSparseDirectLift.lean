import ZFVP.ModelTheory.WoodinSparseThreadLift
import ZFVP.ModelTheory.WoodinRecodedDirectLift
import ZFVP.ModelTheory.WoodinSparseDirectColumns

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ i z p : V} [IsOrdinal θ]
local notation "N" => woodinNormalizedPrefixCode θ
local notation "C" => woodinNormalizedStageCode θ
local notation "Q" => woodinRecodingCarriers (woodinSparseRecodingHistory θ)
local notation "T" => woodinRecodingOrders (woodinSparseRecodingHistory θ)
local notation "m" => woodinRecodingMaps (woodinSparseRecodingHistory θ)

theorem woodinSparseStageMap_direct_lift
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (ih : ∀ j ∈ θ, IsWoodinSparseLiftRow j)
    (hi : i ∈ θ) (hz : z ∈ (forcingCodeP C) ‘ θ) (hp : p ∈ (forcingCodeP C) ‘ i)
    (hle : ⟨p, ((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ) ‘ z⟩ₖ ∈ (forcingCodeR C) ‘ i) :
    (woodinSparseStageMap θ) ‘ (((forcingCodeL C) ‘ ⟨i, θ⟩ₖ) ‘ ⟨z, p⟩ₖ) =
      sparsePrefixReplace (succ (woodinSourceIndex i)) ((woodinSparseStageMap θ) ‘ z)
        ((woodinSparseStageMap i) ‘ p) := by
  have hN := woodinNormalizedPrefixCode_valid hΩ hAC hθ
  obtain ⟨hC, he⟩ := woodinNormalizedStage_through_endpoint hΩ hAC hθ
  have hpN : p ∈ (forcingCodeP N) ‘ i := by
    rwa [← hN.tableP.value_of_subset hC.tableP he.subP hi] at hp
  have hleN : ⟨p, z ‘ i⟩ₖ ∈ (forcingCodeR N) ‘ i := by
    rwa [woodinNormalizedStage_direct_projection hΩ hAC hθ h0 hlim hinac hi hz,
      ← hN.tableR.value_of_subset hC.tableR he.subR hi] at hle
  have hzD := hz
  rw [(woodinNormalized_direct_dictionary hΩ hAC hθ h0 hlim hinac).1] at hzD
  have hzI := forcingDirectLimit_subset _ _ _ _ _ _ hzD
  have hl := (hC.system.lifts.lift i (mem_succ_iff.mpr (Or.inr hi)) θ (mem_succ_self θ)
    (IsOrdinal.toIsTransitive.transitive _ hi) z hz p hp hle).1
  have hrows : ∀ j ∈ θ, IsWoodinSparseRow j (woodinSparseRecodingRec j) :=
    fun j hj ↦ woodinSparseRecodingRec_correct hΩ hAC j (hθ j hj)
  have hm := woodinSparseHistory_family hΩ hAC hθ hrows
  have hT : ∀ j ∈ θ, IsForcingPreorder (Q ‘ j) (T ‘ j) :=
    fun _ hj ↦ woodinSparseHistory_preorder hrows hj
  have hQt := (woodinSparseRecodingHistory_tables θ).1
  have hTt := (woodinSparseRecodingHistory_tables θ).2.1
  have hsp : ∀ j ∈ θ, ∀ q ∈ Q ‘ j, IsSparseFunctionOn (succ (woodinSourceIndex j)) q :=
    fun _ hj _ hq ↦ woodinSparseHistory_sparse hrows hj hq
  have hπ : ∀ j ∈ θ, ∀ k ∈ θ, j ∈ k → ∀ q ∈ Q ‘ k,
      ((forcingRecodedProjections θ N m) ‘ ⟨j, k⟩ₖ) ‘ q = q ↾ (succ (woodinSourceIndex j)) := by
    intro j hj k hk hjk q hq
    let := IsOrdinal.of_mem hk
    exact woodinSparseHistory_projection hΩ hAC hθ hrows hj hk (IsOrdinal.toIsTransitive.transitive _ hjk) hq
  have hE : ∀ j ∈ θ, ∀ k ∈ θ, j ⊆ k → ∀ q ∈ Q ‘ j,
      ((forcingRecodedSections θ N m) ‘ ⟨j, k⟩ₖ) ‘ q = q :=
    fun _ hj _ hk hjk _ hq ↦ woodinSparseHistory_section hΩ hAC hθ hrows hj hk hjk hq
  rw [woodinSparseStageMap_direct h0 hlim hinac, woodinSparsePrefixCode,
    woodinSparseDirectMap_value hΩ hAC hθ hm hT hQt hTt h0 hlim hsp hπ hE hinac hl,
    woodinSparseDirectMap_value hΩ hAC hθ hm hT hQt hTt h0 hlim hsp hπ hE hinac hz,
    woodinNormalizedStage_direct_lift hΩ hAC hθ h0 hlim hinac hi hz hpN]
  exact woodinSparseThreadSplice_union hΩ hAC hθ ih hzI hi hpN hleN

end ZFVP
