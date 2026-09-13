import ZFVP.ModelTheory.WoodinSourceEndpoint
import ZFVP.ModelTheory.WoodinInitialSeedQuotientClosure
import ZFVP.ModelTheory.QuotientClosureCompositionTransfer

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem functions_into_singleton_eq {P a f g : V}
    (hf : f ∈ ({a} : V) ^ P) (hg : g ∈ ({a} : V) ^ P) : f = g := by
  let := IsFunction.of_mem hf
  let := IsFunction.of_mem hg
  apply functions_eq_of_domain_values
  · exact (domain_eq_of_mem_function hf).trans (domain_eq_of_mem_function hg).symm
  · intro p hp
    have hpP := (domain_eq_of_mem_function hf) ▸ hp
    exact (mem_singleton_iff.mp (function_value_mem hf hpP)).trans
      (mem_singleton_iff.mp (function_value_mem hg hpP)).symm

theorem woodinInitialStage_seed_quotient_closedBelow_map {δ π : V} (hδ : IsWoodinSupercompact δ)
    (hπ : π ∈ (woodinStagePoset (woodinSeedStage : V)) ^ (woodinStagePoset (woodinInitialStage : V))) :
    ForcesProjectionQuotientClosedBelow (woodinStagePoset (woodinSeedStage : V))
      (woodinStageOrder (woodinSeedStage : V)) (woodinStageTop (woodinSeedStage : V))
      (woodinStagePoset (woodinInitialStage : V)) (woodinStageOrder (woodinInitialStage : V))
      π woodinSeedCardinal := by
  let ρ := twoStepProjection (woodinStagePoset (woodinSeedStage : V))
    (woodinStageOrder (woodinSeedStage : V))
    (saturatedWoodinPrefixPosetName (woodinStagePoset (woodinSeedStage : V))
      (woodinStageOrder (woodinSeedStage : V)) (woodinStageTop (woodinSeedStage : V))
      (woodinStageCardinal (woodinSeedStage : V)) (woodinStageCardinal (woodinInitialStage : V))) ∅
  have hρ : ρ ∈ (woodinStagePoset (woodinSeedStage : V)) ^ (woodinStagePoset (woodinInitialStage : V)) := by
    simpa only [ρ, woodinInitialStage, woodinSuccessorStep, woodinSuccessorAt,
      woodinStagePoset_code, woodinStageCardinal_code] using
      twoStepProjection_maps (woodinStagePoset (woodinSeedStage : V)) (woodinStageOrder (woodinSeedStage : V))
        (saturatedWoodinPrefixPosetName (woodinStagePoset (woodinSeedStage : V))
          (woodinStageOrder (woodinSeedStage : V)) (woodinStageTop (woodinSeedStage : V))
          (woodinStageCardinal (woodinSeedStage : V)) (woodinStageCardinal (woodinInitialStage : V))) ∅
  have hπ' : π ∈ ({∅} : V) ^ (woodinStagePoset (woodinInitialStage : V)) := by
    simpa only [woodinSeedStage, woodinStagePoset_code] using hπ
  have hρ' : ρ ∈ ({∅} : V) ^ (woodinStagePoset (woodinInitialStage : V)) := by
    simpa only [woodinSeedStage, woodinStagePoset_code] using hρ
  have he : π = ρ := functions_into_singleton_eq hπ' hρ'
  rw [he]
  simpa only [ρ, woodinSeedStage, woodinStagePoset_code, woodinStageOrder_code,
    woodinStageTop_code, woodinStageCardinal_code] using woodinInitialStage_seed_quotient_closedBelow hδ

theorem woodinSourceCode_seed_first_quotient {δ θ s : V} [IsOrdinal θ]
    (hδ : IsWoodinSupercompact δ) (hs : IsForcingIterationCode θ s) (h0 : (∅ : V) ∈ θ)
    (hP0 : (forcingCodeP s) ‘ ∅ = woodinStagePoset (woodinInitialStage : V))
    (hR0 : (forcingCodeR s) ‘ ∅ = woodinStageOrder (woodinInitialStage : V)) :
    IterationQuotientClosedBelow (woodinSourceCode θ s) ∅ (woodinSourceIndex ∅) woodinSeedCardinal := by
  have hs' := woodinSourceCode_valid hs
  have hz : (∅ : V) ∈ woodinSourceIndex θ :=
    subset_ordinalAdd 1 θ ∅ (by change (0 : V) ∈ succ 0; simp)
  have hi := woodinSourceIndex_mem_iff.mpr h0
  have hp := (hs'.system.projection hz hi (empty_subset _)).maps
  have hh := woodinInitialStage_seed_quotient_closedBelow_map hδ (π :=
    (forcingCodeπ (woodinSourceCode θ s)) ‘ ⟨∅, woodinSourceIndex ∅⟩ₖ) (by
      simpa only [woodinSourceCode, forcingCodeP_code, woodinInsertSeed_zero,
        woodinInsertSeed_at_sourceIndex h0, hP0, woodinSeedStage, woodinStagePoset_code] using hp)
  simpa only [IterationQuotientClosedBelow, woodinSourceCode, forcingCodeP_code, forcingCodeR_code,
    forcingCodet_code, woodinInsertSeed_zero, woodinInsertSeed_at_sourceIndex h0, hP0, hR0,
    woodinSeedStage, woodinStagePoset_code, woodinStageOrder_code, woodinStageTop_code] using hh

theorem woodinSourceCode_seed_positive_quotient {δ θ s K j : V} [IsOrdinal θ]
    (hδ : IsWoodinSupercompact δ) (hs : IsForcingIterationCode θ s)
    (hQ : HasWoodinQuotientClosure θ s K) (h0 : (∅ : V) ∈ θ) (hj : j ∈ θ)
    (hP0 : (forcingCodeP s) ‘ ∅ = woodinStagePoset (woodinInitialStage : V))
    (hR0 : (forcingCodeR s) ‘ ∅ = woodinStageOrder (woodinInitialStage : V))
    (hK0 : K ‘ ∅ = woodinStageCardinal (woodinInitialStage : V)) :
    IterationQuotientClosedBelow (woodinSourceCode θ s) ∅ (woodinSourceIndex j) woodinSeedCardinal := by
  let := IsOrdinal.of_mem hj
  have hs' := woodinSourceCode_valid hs
  have hz : (∅ : V) ∈ woodinSourceIndex θ :=
    subset_ordinalAdd 1 θ ∅ (by change (0 : V) ∈ succ 0; simp)
  have hi := woodinSourceIndex_mem_iff.mpr h0
  have hj' := woodinSourceIndex_mem_iff.mpr hj
  have hij : woodinSourceIndex (∅ : V) ⊆ woodinSourceIndex j := ordinalAdd_mono_right 1 (empty_subset j)
  have hbase := woodinSourceCode_seed_first_quotient hδ hs h0 hP0 hR0
  have htail := woodinSourceCode_positive_quotient hQ h0 hj (empty_subset j)
  rw [woodinSourceCardinals_stage h0] at htail
  have hn := woodinSuccessorStep_preserves_below_supercompact woodinSeedStage_stage woodinSeedStage_small hδ
    (by simpa only [woodinSeedStage, woodinStageCardinal_code] using woodinSeedCardinal_lt hδ)
  have hμ : woodinSeedCardinal ⊆ K ‘ ∅ := by
    rw [hK0]
    let : IsOrdinal (woodinStageCardinal (woodinInitialStage : V)) := hn.2.2.1.1
    apply IsOrdinal.toIsTransitive.transitive
    simpa only [woodinInitialStage, woodinSeedStage, woodinStageCardinal_code] using hn.2.2.2.1
  have htail' := projectionQuotient_closedBelow_mono_forced
    (hs'.system.order.preorder _ hi) (hs'.system.tops.top _ hi)
    (hs'.system.order.preorder _ hj') (hs'.system.projection hi hj' hij) hμ htail
  exact projectionQuotient_closedBelow_comp_forced
    (hs'.system.order.preorder _ hz) (hs'.system.tops.top _ hz)
    (hs'.system.splitProjection hz hi (empty_subset _))
    (hs'.system.order.preorder _ hi) (hs'.system.tops.top _ hi)
    (hs'.system.order.preorder _ hj') (hs'.system.projection hz hj' (empty_subset _))
    (hs'.system.projection hi hj' hij)
    (hs'.system.split.projComp _ hz _ hi _ hj' (empty_subset _) hij) hbase htail'

theorem woodinSourceCode_quotient_closure {δ θ s K : V} [IsOrdinal θ]
    (hδ : IsWoodinSupercompact δ) (hs : IsForcingIterationCode θ s)
    (hQ : HasWoodinQuotientClosure θ s K) (h0 : (∅ : V) ∈ θ)
    (hP0 : (forcingCodeP s) ‘ ∅ = woodinStagePoset (woodinInitialStage : V))
    (hR0 : (forcingCodeR s) ‘ ∅ = woodinStageOrder (woodinInitialStage : V))
    (hK0 : K ‘ ∅ = woodinStageCardinal (woodinInitialStage : V)) :
    HasWoodinQuotientClosure (woodinSourceIndex θ) (woodinSourceCode θ s) (woodinSourceCardinals θ K) := by
  intro i hi j hj hij
  rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
  · rw [woodinSourceCardinals_seed]
    rcases woodinSourceIndex_cases hj with rfl | ⟨b, hb, rfl⟩
    · exact (woodinSourceCode_valid hs).diagonal_quotient_closedBelow hi _
    · exact woodinSourceCode_seed_positive_quotient hδ hs hQ h0 hb hP0 hR0 hK0
  · let := IsOrdinal.of_mem ha
    rcases woodinSourceIndex_cases hj with rfl | ⟨b, hb, rfl⟩
    · have he : woodinSourceIndex a = ∅ := SetTheory.subset_antisymm hij (empty_subset _)
      exact False.elim (woodinSourceIndex_nonzero a he)
    · let := IsOrdinal.of_mem hb
      apply woodinSourceCode_positive_quotient hQ ha hb
      rcases IsOrdinal.subset_iff.mp hij with he | hm
      · exact IsOrdinal.subset_iff.mpr (Or.inl (woodinSourceIndex_injective he))
      · exact IsOrdinal.subset_iff.mpr (Or.inr (woodinSourceIndex_mem_iff.mp hm))

theorem woodinIterationPrefix_initial_stage {δ θ : V} [IsOrdinal θ]
    (h : IsWoodinIterationHistory δ θ (woodinHistoryCodes (woodinIterationHistory θ))
      (woodinHistoryCardinals (woodinIterationHistory θ))) (h0 : (∅ : V) ∈ θ) :
    woodinIterationStage (woodinIterationPrefix θ) (woodinIterationCardinalPrefix θ) ∅ = woodinInitialStage := by
  change woodinIterationStage (forcingIterationCodeUnion θ (woodinHistoryCodes (woodinIterationHistory θ)))
    (woodinHistoryCardinalUnion θ (woodinHistoryCardinals (woodinIterationHistory θ))) ∅ = _
  rw [h.union_stage h0 (mem_succ_self ∅), woodinIterationHistory_code_value h0,
    woodinIterationHistory_cardinal_value h0, woodinIterationRec_initial,
    kpair.π₁_kpair, kpair.π₂_kpair, woodinInitialCode_stage]

theorem woodinSourceCode_actual_prefix_quotient_closure {δ θ : V} [IsOrdinal θ]
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) (hθ : θ ⊆ δ) (h0 : (∅ : V) ∈ θ) :
    HasWoodinQuotientClosure (woodinSourceIndex θ) (woodinSourceCode θ (woodinIterationPrefix θ))
      (woodinSourceCardinals θ (woodinIterationCardinalPrefix θ)) := by
  have hx := woodinIterationExit hδ hAC
  have hs := fun i hi ↦ (hx.2.1 i (hθ i hi)).1
  have hh := woodinIterationHistory_of_stages hs
  have he := woodinIterationPrefix_initial_stage hh h0
  have hc : IsForcingIterationCode θ (woodinIterationPrefix θ) := hh.codes.union_code
  apply woodinSourceCode_quotient_closure hδ hc
    (woodinIterationPrefix_quotient_closure hs (fun i hi ↦ (hx.2.1 i (hθ i hi)).2)) h0
  · simpa only [woodinIterationStage, woodinStagePoset_code] using congrArg woodinStagePoset he
  · simpa only [woodinIterationStage, woodinStageOrder_code] using congrArg woodinStageOrder he
  · simpa only [woodinIterationStage, woodinStageCardinal_code] using congrArg woodinStageCardinal he

theorem woodinSourceCode_actual_full_quotient_closure {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    HasWoodinQuotientClosure (woodinSourceIndex (succ δ))
      (woodinSourceCode (succ δ) (kpair.π₁ (woodinIterationRec δ)))
      (woodinSourceCardinals (succ δ) (kpair.π₂ (woodinIterationRec δ))) := by
  let := hδ.inaccessible.1
  have hx := woodinIterationExit hδ hAC
  have hv := woodinIteration_endpoint_valid hδ hAC
  have h0 : (∅ : V) ∈ δ := IsOrdinal.toIsTransitive.mem_trans (by simp) hδ.inaccessible.2.1
  have he0 := woodinIterationPrefix_initial_stage
    (woodinIterationHistory_of_stages (fun i hi ↦ (hx.2.1 i hi).1)) h0
  have he : woodinIterationStage (kpair.π₁ (woodinIterationRec δ)) (kpair.π₂ (woodinIterationRec δ)) ∅ =
      woodinInitialStage := by
    rw [woodinIteration_endpoint_direct hδ hAC, kpair.π₁_kpair, kpair.π₂_kpair]
    simpa only [woodinIterationStage, forcingDirectCode, forcingThreadCode, forcingIterationCodeNext,
      forcingCodeP_code, forcingCodeR_code, forcingCodet_code, forcingFamilyNext_old h0] using he0
  apply woodinSourceCode_quotient_closure hδ hv.1.code hv.2 (mem_succ_iff.mpr (Or.inr h0))
  · simpa only [woodinIterationStage, woodinStagePoset_code] using congrArg woodinStagePoset he
  · simpa only [woodinIterationStage, woodinStageOrder_code] using congrArg woodinStageOrder he
  · simpa only [woodinIterationStage, woodinStageCardinal_code] using congrArg woodinStageCardinal he

end ZFVP
