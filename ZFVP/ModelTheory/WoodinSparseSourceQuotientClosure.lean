import ZFVP.ModelTheory.WoodinSparseSeedQuotient

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal θ]

theorem woodinSparseSourcePrefixCode_quotient_closure
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (h0 : (∅ : V) ∈ θ) :
    HasWoodinQuotientClosure (woodinSourceIndex θ) (woodinSparseSourcePrefixCode θ)
      (woodinSparseSourcePrefixCardinals θ) := by
  have hs := woodinSparsePrefixCode_valid hΩ hAC hθ
  have he := woodinSparsePrefixCode_stage_eq hΩ hAC hθ h0
  have hP0 : (forcingCodeP (woodinSparsePrefixCode θ)) ‘ ∅ =
      (forcingCodeP (woodinSparseStageCode (∅ : V))) ‘ ∅ := by
    simpa only [woodinIterationStage, woodinStagePoset_code] using congrArg woodinStagePoset he
  have hR0 : (forcingCodeR (woodinSparsePrefixCode θ)) ‘ ∅ =
      (forcingCodeR (woodinSparseStageCode (∅ : V))) ‘ ∅ := by
    simpa only [woodinIterationStage, woodinStageOrder_code] using congrArg woodinStageOrder he
  have hfirst : (woodinSeedCardinal : V) ∈ (woodinIterationCardinalPrefix θ) ‘ ∅ := by
    rw [woodinIterationCardinalPrefix_initial
      (woodinIterationHistory_of_stages (fun j hj ↦ ((woodinIterationExit hΩ hAC).2.1 j (hθ j hj)).1)) h0]
    exact woodinSeedCardinal_lt_initial hΩ
  let := ((woodinSparsePrefixCode_invariant hΩ hAC hθ).inaccessible ∅ h0).1
  exact woodinSourceCode_quotient_closure_of_seed hs (woodinSparsePrefixCode_quotient_closure hΩ hAC hθ) h0
    (IsOrdinal.toIsTransitive.transitive _ hfirst)
    (woodinSourceCode_seed_first_sparse_quotient hΩ hAC hs h0 hP0 hR0)

theorem woodinSparseSourceStageCode_quotient_closure
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    HasWoodinQuotientClosure (succ (woodinSourceIndex θ)) (woodinSparseSourceStageCode θ)
      (woodinSparseSourceStageCardinals θ) := by
  have h0 : (∅ : V) ∈ succ θ := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (empty_subset θ))
  have hs := woodinSparseStageCode_valid hΩ hAC hθ
  have hfirst := woodinIterationRec_seed_cardinal_lt hΩ hAC hθ
  have hκ : IsOrdinal ((kpair.π₂ (woodinIterationRec θ)) ‘ ∅) := by
    rw [woodinIterationRec_old_cardinal hΩ hAC hθ h0]
    simpa only [woodinIterationStage, woodinStageCardinal_code] using
      (woodinIterationRec_stage_le hΩ hAC (empty_subset Ω)).2.2.1
  let := hκ
  have hh := woodinSourceCode_quotient_closure_of_seed hs
    (woodinSparseStageCode_quotient_closure hΩ hAC hθ) h0 (IsOrdinal.toIsTransitive.transitive _ hfirst)
    (woodinSourceCode_seed_first_sparse_quotient hΩ hAC hs h0
      (woodinSparseStage_old_row h0).1 (woodinSparseStage_old_row h0).2)
  simpa only [woodinSourceIndex_successor, woodinSparseSourceStageCode, woodinSparseSourceStageCardinals] using hh

end ZFVP
