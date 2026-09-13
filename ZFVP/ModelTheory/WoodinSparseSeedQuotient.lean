import ZFVP.ModelTheory.WoodinSparseQuotientForcing
import ZFVP.ModelTheory.WoodinSeedQuotientComposition
import ZFVP.ModelTheory.SameBaseQuotientForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingProjection_to_singleton {a Q S f : V}
    (hS : IsForcingPreorder Q S) (hf : f ∈ ({a} : V) ^ Q) :
    IsForcingProjection {a} (({a} : V) ×ˢ {a}) Q S f := by
  refine ⟨hf, ?_, ?_⟩
  · intro p hp q hq _
    exact kpair_mem_iff.mpr ⟨function_value_mem hf hp, function_value_mem hf hq⟩
  · intro q hq p hp _
    exact ⟨q, hq, hS.2.1 q hq,
      (mem_singleton_iff.mp (function_value_mem hf hq)).trans (mem_singleton_iff.mp hp).symm⟩

theorem woodinSparseInitial_seed_quotient_closedBelow_map {Ω ρ : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
    (hρ : ρ ∈ ({∅} : V) ^ ((forcingCodeP (woodinSparseStageCode (∅ : V))) ‘ ∅)) :
    ForcesProjectionQuotientClosedBelow ({∅} : V) (({∅} : V) ×ˢ {∅}) ∅
      ((forcingCodeP (woodinSparseStageCode (∅ : V))) ‘ ∅)
      ((forcingCodeR (woodinSparseStageCode (∅ : V))) ‘ ∅) ρ woodinSeedCardinal := by
  let Q := (forcingCodeP (kpair.π₁ (woodinIterationRec (∅ : V)) )) ‘ ∅
  let S := (forcingCodeR (kpair.π₁ (woodinIterationRec (∅ : V)) )) ‘ ∅
  let π := definableGraph Q (fun _ : V ↦ (∅ : V)) (by definability)
  have hπ : π ∈ ({∅} : V) ^ Q :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ _ ↦ by simp)
  have hS : IsForcingPreorder Q S :=
    (woodinIterationStageCode_valid_le hΩ hAC (empty_subset Ω)).system.order.preorder ∅ (mem_succ_self ∅)
  have hL := (woodinSparseStageCode_valid hΩ hAC (empty_subset Ω)).system.order.preorder ∅ (mem_succ_self ∅)
  have hclosed : ForcesProjectionQuotientClosedBelow ({∅} : V) (({∅} : V) ×ˢ {∅}) ∅ Q S π woodinSeedCardinal := by
    have hπ' : π ∈ (woodinStagePoset (woodinSeedStage : V)) ^ (woodinStagePoset (woodinInitialStage : V)) := by
      simpa only [Q, woodinIterationRec_initial, kpair.π₁_kpair, woodinInitialCode, forcingInitialCode,
        forcingCodeP_code, forcingFamilyNext_new, woodinSeedStage, woodinStagePoset_code] using hπ
    simpa only [Q, S, woodinIterationRec_initial, kpair.π₁_kpair, woodinInitialCode, forcingInitialCode,
      forcingCodeP_code, forcingCodeR_code, forcingFamilyNext_new, woodinSeedStage,
      woodinStagePoset_code, woodinStageOrder_code, woodinStageTop_code] using
      woodinInitialStage_seed_quotient_closedBelow_map hΩ hπ'
  apply sameBase_quotient_closedBelow_forced
    (show IsForcingPreorder ({∅} : V) (({∅} : V) ×ˢ {∅}) by
      simpa only [woodinSeedStage, woodinStagePoset_code, woodinStageOrder_code] using (woodinSeedStage_stage (V := V)).1)
    (show IsForcingTop ({∅} : V) (({∅} : V) ×ˢ {∅}) ∅ by
      simpa only [woodinSeedStage, woodinStagePoset_code, woodinStageOrder_code, woodinStageTop_code] using
        (woodinSeedStage_stage (V := V)).2.1)
    (forcingProjection_to_singleton hS hπ) hS (forcingProjection_to_singleton hL hρ) hL
    (woodinSparseRealizationMap_projection hΩ hAC (empty_subset Ω)).maps
    (woodinSparseRealizationInverse_maps hΩ hAC (empty_subset Ω))
    (fun _ hq ↦ woodinSparseRealizationMap_right_inverse hΩ hAC (empty_subset Ω) hq)
    (fun _ hp _ hq ↦ (woodinSparseRealizationMap_order_iff hΩ hAC (empty_subset Ω) hp hq).symm)
    ?_ hclosed
  intro p hp
  exact (mem_singleton_iff.mp (function_value_mem hρ
    (function_value_mem (woodinSparseRealizationMap_projection hΩ hAC (empty_subset Ω)).maps hp))).trans
    (mem_singleton_iff.mp (function_value_mem hπ hp)).symm

theorem woodinSourceCode_seed_first_sparse_quotient {Ω θ s : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
    (hs : IsForcingIterationCode θ s) (h0 : (∅ : V) ∈ θ)
    (hP0 : (forcingCodeP s) ‘ ∅ = (forcingCodeP (woodinSparseStageCode (∅ : V))) ‘ ∅)
    (hR0 : (forcingCodeR s) ‘ ∅ = (forcingCodeR (woodinSparseStageCode (∅ : V))) ‘ ∅) :
    IterationQuotientClosedBelow (woodinSourceCode θ s) ∅ (woodinSourceIndex ∅) woodinSeedCardinal := by
  have hs' := woodinSourceCode_valid hs
  have hz : (∅ : V) ∈ woodinSourceIndex θ :=
    subset_ordinalAdd 1 θ ∅ (by change (0 : V) ∈ succ 0; simp)
  have hi := woodinSourceIndex_mem_iff.mpr h0
  have hp := (hs'.system.projection hz hi (empty_subset _)).maps
  have hh := woodinSparseInitial_seed_quotient_closedBelow_map hΩ hAC (ρ :=
    (forcingCodeπ (woodinSourceCode θ s)) ‘ ⟨∅, woodinSourceIndex ∅⟩ₖ) (by
      simpa only [woodinSourceCode, forcingCodeP_code, woodinInsertSeed_zero,
        woodinInsertSeed_at_sourceIndex h0, hP0] using hp)
  simpa only [IterationQuotientClosedBelow, woodinSourceCode, forcingCodeP_code, forcingCodeR_code,
    forcingCodet_code, woodinInsertSeed_zero, woodinInsertSeed_at_sourceIndex h0, hP0, hR0] using hh

end ZFVP
