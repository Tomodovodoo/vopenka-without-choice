import ZFVP.ModelTheory.WoodinRecodedConstruction
import ZFVP.ModelTheory.WoodinNormalizedEndpoint

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinRecodingRec_endpoint_correct {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    IsWoodinRecodedRow Ω (woodinRecodingRec Ω) := by
  let := hΩ.inaccessible.1
  obtain ⟨hz, hlim, hinac⟩ := woodinEndpoint_branch hΩ hAC
  let Q := woodinRecodingCarriers (woodinRecodingHistory Ω)
  let T := woodinRecodingOrders (woodinRecodingHistory Ω)
  let m := woodinRecodingMaps (woodinRecodingHistory Ω)
  let c := woodinRecodedPrefixCode Ω
  have hm := woodinRecodedPrefix_family hΩ hAC (subset_refl Ω)
  have hT := woodinRecodedPrefix_preorders hΩ hAC (subset_refl Ω)
  have ht := woodinRecodingHistory_tables Ω
  have hf := woodinRecodedDirectMap_isomorphism hΩ hAC (subset_refl Ω) hz hlim hinac hm hT ht.1 ht.2.1
  have hR := (woodinNormalizedStageCode_endpoint_valid hΩ hAC).system.order.preorder Ω (mem_succ_self Ω)
  rw [woodinRecodingRec_rule]
  change IsWoodinRecodedRow Ω (woodinRecodingRowRule Ω c m)
  simp only [woodinRecodingRowRule, ite_eq_right hz, ite_eq_right hlim, ite_eq_left hinac,
    IsWoodinRecodedRow, woodinRecodingDirectRow, kpair.π₁_kpair, kpair.π₂_kpair]
  refine ⟨hf, hf.target_preorder hR ?_, ?_⟩
  · unfold forcingSparseOrder forcingPullbackOrder
    exact sep_subset
  intro ξ hξ hcard
  let := hξ.1
  have hQΩ : ∀ i ∈ Ω, (forcingCodeP c) ‘ i ∈ hierarchy Ω := by
    intro i hi
    apply woodinRecodedPrefixCode_small hΩ hAC (subset_refl Ω) hi hΩ.inaccessible
    exact ((woodinIterationExit hΩ hAC).2.1 i hi).1.bounded i (mem_succ_self i)
  have hb := forcingSparseCodes_subset_hierarchy (U := forcingCodeUniverse c)
    (ordinal_limit_of_not_successor hlim) hQΩ
  apply subset_mem_hierarchy_limit hξ.rankCriterion.2.2.1 ?_ hb
  rw [mem_hierarchy_iff_rank_mem, rank_hierarchy]
  exact woodinIteration_endpoint_cardinal hΩ hAC ▸ hcard

noncomputable def woodinRecodedStageCode (θ : V) : V :=
  forcingRecodedCode (succ θ) (woodinNormalizedStageCode θ)
    (woodinRecodingCarriers (woodinRecodingHistory (succ θ)))
    (woodinRecodingOrders (woodinRecodingHistory (succ θ)))
    (woodinRecodingMaps (woodinRecodingHistory (succ θ)))

instance woodinRecodedStageCode_definable : ℒₛₑₜ-function₁[V] woodinRecodedStageCode := by
  unfold woodinRecodedStageCode
  apply Language.DefinableFunction₅.comp <;> definability

theorem woodinRecodedStageCode_endpoint_family {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    ∀ i ∈ succ Ω, IsForcingIsomorphism ((forcingCodeP (woodinNormalizedStageCode Ω)) ‘ i)
      ((forcingCodeR (woodinNormalizedStageCode Ω)) ‘ i)
      ((woodinRecodingCarriers (woodinRecodingHistory (succ Ω))) ‘ i)
      ((woodinRecodingOrders (woodinRecodingHistory (succ Ω))) ‘ i)
      ((woodinRecodingMaps (woodinRecodingHistory (succ Ω))) ‘ i) := by
  let := hΩ.inaccessible.1
  have he := woodinNormalizedStageCode_endpoint_extends hΩ hAC
  have hs := woodinNormalizedPrefixCode_valid hΩ hAC (subset_refl Ω)
  have hz := woodinNormalizedStageCode_endpoint_valid hΩ hAC
  intro i hi
  rw [(woodinRecodingHistory_values hi).1, (woodinRecodingHistory_values hi).2.1,
    (woodinRecodingHistory_values hi).2.2]
  rcases mem_succ_iff.mp hi with rfl | hi
  · exact (woodinRecodingRec_endpoint_correct hΩ hAC).1
  · rw [← hs.tableP.value_of_subset hz.tableP he.subP hi,
      ← hs.tableR.value_of_subset hz.tableR he.subR hi,
      (woodinNormalizedPrefix_row hΩ hAC (subset_refl Ω) hi).1,
      (woodinNormalizedPrefix_row hΩ hAC (subset_refl Ω) hi).2]
    exact (woodinRecodingRec_correct hΩ hAC i hi).1

theorem woodinRecodedStageCode_endpoint_valid {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    IsForcingIterationCode (succ Ω) (woodinRecodedStageCode Ω) := by
  let := hΩ.inaccessible.1
  apply forcingRecoded_code (woodinNormalizedStageCode_endpoint_valid hΩ hAC)
    (woodinRecodedStageCode_endpoint_family hΩ hAC) ?_
    (woodinRecodingHistory_tables (succ Ω)).1 (woodinRecodingHistory_tables (succ Ω)).2.1
  intro i hi
  rw [(woodinRecodingHistory_values hi).1, (woodinRecodingHistory_values hi).2.1]
  rcases mem_succ_iff.mp hi with rfl | hi
  · exact (woodinRecodingRec_endpoint_correct hΩ hAC).2.1
  · exact (woodinRecodingRec_correct hΩ hAC i hi).2.1

theorem woodinRecodedStageCode_endpoint_extends {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    ForcingCodeExtends (woodinRecodedPrefixCode Ω) (woodinRecodedStageCode Ω) := by
  let := hΩ.inaccessible.1
  have hsub : Ω ⊆ succ Ω := fun _ hi ↦ mem_succ_iff.mpr (Or.inr hi)
  exact forcingRecoded_extends (woodinNormalizedPrefixCode_valid hΩ hAC (subset_refl Ω))
    (woodinNormalizedStageCode_endpoint_valid hΩ hAC) (woodinNormalizedStageCode_endpoint_extends hΩ hAC) hsub
    (fun i hi ↦ (woodinRecodingHistory_agrees hi (hsub i hi)).1)
    (fun i hi ↦ (woodinRecodingHistory_agrees hi (hsub i hi)).2.1)
    (fun i hi ↦ (woodinRecodingHistory_agrees hi (hsub i hi)).2.2)
    (woodinRecodedPrefixCode_valid hΩ hAC (subset_refl Ω)) (woodinRecodedStageCode_endpoint_valid hΩ hAC)

end ZFVP
