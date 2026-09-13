import ZFVP.ModelTheory.WoodinSparseStageInvariant
import ZFVP.ModelTheory.WoodinSourceInvariant

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal θ]

theorem woodinSparsePrefixCode_stage_eq
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i : V} (hi : i ∈ θ) :
    woodinIterationStage (woodinSparsePrefixCode θ) (woodinIterationCardinalPrefix θ) i =
      woodinIterationStage (woodinSparseStageCode i) (kpair.π₂ (woodinIterationRec i)) i := by
  let := IsOrdinal.of_mem hi
  have hisub : i ⊆ Ω := fun x hx ↦ hθ x (IsOrdinal.toIsTransitive.transitive _ hi x hx)
  have hcard := woodinSparseSourcePrefixCardinals_value hΩ hAC hθ hi
  rw [woodinSparseSourcePrefixCardinals, woodinSourceCardinals_stage hi] at hcard
  unfold woodinIterationStage
  rw [hcard, woodinSparsePrefixCode_top hΩ hAC hθ hi, woodinSparseStageCode_top hΩ hAC hisub]
  simp only [woodinSparsePrefixCode, woodinSparseStageCode, forcingRecodedCode, forcingCodeP_code,
    forcingCodeR_code, (woodinSparseRecodingHistory_values hi).1, (woodinSparseRecodingHistory_values hi).2.1,
    (woodinSparseRecodingHistory_values (mem_succ_self i)).1,
    (woodinSparseRecodingHistory_values (mem_succ_self i)).2.1]

theorem woodinSparsePrefixCode_invariant
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    IsWoodinIteration Ω θ (woodinSparsePrefixCode θ) (woodinIterationCardinalPrefix θ) := by
  have hr := woodinIterationPrefix_of_stages
    (fun j hj ↦ ((woodinIterationExit hΩ hAC).2.1 j (hθ j hj)).1)
  refine ⟨woodinSparsePrefixCode_valid hΩ hAC hθ, hr.cardinals, ?_, ?_, hr.inaccessible, hr.bounded, hr.increasing⟩
  · intro i hi
    let := IsOrdinal.of_mem hi
    rw [woodinSparsePrefixCode_stage_eq hΩ hAC hθ hi]
    exact woodinSparseStageCode_stage hΩ hAC (fun x hx ↦ hθ x (IsOrdinal.toIsTransitive.transitive _ hi x hx))
  · intro i hi
    let := IsOrdinal.of_mem hi
    rw [woodinSparsePrefixCode_stage_eq hΩ hAC hθ hi]
    exact woodinSparseStageCode_stage_small hΩ hAC (fun x hx ↦ hθ x (IsOrdinal.toIsTransitive.transitive _ hi x hx))

theorem woodinSparseSourcePrefixCode_invariant
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (h0 : (∅ : V) ∈ θ) :
    IsWoodinSourceInvariant Ω (woodinSourceIndex θ) (woodinSparseSourcePrefixCode θ)
      (woodinSparseSourcePrefixCardinals θ) := by
  apply woodinSourceCode_invariant (woodinSparsePrefixCode_invariant hΩ hAC hθ) h0 (woodinSeedCardinal_lt hΩ)
  rw [woodinIterationCardinalPrefix_initial
    (woodinIterationHistory_of_stages (fun j hj ↦ ((woodinIterationExit hΩ hAC).2.1 j (hθ j hj)).1)) h0]
  exact woodinSeedCardinal_lt_initial hΩ

theorem woodinIterationRec_seed_cardinal_lt
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    (woodinSeedCardinal : V) ∈ (kpair.π₂ (woodinIterationRec θ)) ‘ ∅ := by
  have h0 : (∅ : V) ∈ succ θ := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (empty_subset θ))
  have he := woodinSparseSourceStageCardinals_value hΩ hAC hθ h0
  rw [woodinSparseSourceStageCardinals, woodinSourceCardinals_stage h0,
    woodinIterationRec_initial, kpair.π₂_kpair, woodinInitialCardinals, forcingFamilyNext_new] at he
  rw [he]
  exact woodinSeedCardinal_lt_initial hΩ

theorem woodinSparseSourceStageCode_invariant
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω) :
    IsWoodinSourceInvariant Ω (succ (woodinSourceIndex θ)) (woodinSparseSourceStageCode θ)
      (woodinSparseSourceStageCardinals θ) := by
  let := hΩ.inaccessible.1
  have h0 : (∅ : V) ∈ succ θ := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (empty_subset θ))
  simpa only [woodinSourceIndex_successor, woodinSparseSourceStageCode, woodinSparseSourceStageCardinals] using
    woodinSourceCode_invariant (woodinSparseStageCode_invariant hΩ hAC hθ) h0 (woodinSeedCardinal_lt hΩ)
      (woodinIterationRec_seed_cardinal_lt hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hθ))

theorem woodinSparseSourceStageCode_endpoint_invariant
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    IsWoodinSourceInvariant (succ Ω) (succ (woodinSourceIndex Ω)) (woodinSparseSourceStageCode Ω)
      (woodinSparseSourceStageCardinals Ω) := by
  let := hΩ.inaccessible.1
  have h0 : (∅ : V) ∈ succ Ω := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (empty_subset Ω))
  simpa only [woodinSourceIndex_successor, woodinSparseSourceStageCode, woodinSparseSourceStageCardinals] using
    woodinSourceCode_invariant (woodinSparseStageCode_endpoint_invariant hΩ hAC) h0
      (mem_succ_iff.mpr (Or.inr (woodinSeedCardinal_lt hΩ)))
      (woodinIterationRec_seed_cardinal_lt hΩ hAC (subset_refl Ω))

end ZFVP

