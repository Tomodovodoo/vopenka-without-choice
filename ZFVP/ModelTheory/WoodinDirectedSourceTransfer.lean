import ZFVP.ModelTheory.WoodinDirectedSparseTransfer
import ZFVP.ModelTheory.WoodinDirectedSeedTransfer

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The actual inserted-seed quotient in any internal ZF model. The fixed raw
seed forcing statement is transported along the normalization comparison. -/
theorem ForcingContext.woodinSparseSource_seed_directedClosedBelow_zf
    (A : ForcingContext V) {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hP : A.P = ({∅} : V)) (hR : A.R = (({∅} : V) ×ˢ {∅})) (ho : A.one = ∅) :
    ∀ α ∈ A.check (woodinSeedCardinal : V),
      IsForcingDirectedClosedAt
        (A.projectionQuotient ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
          ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨∅, woodinSourceIndex θ⟩ₖ))
        (forcingSeparativeOrder
          (A.projectionQuotient ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
            ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨∅, woodinSourceIndex θ⟩ₖ))
          (A.projectionQuotientOrder ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
            ((forcingCodeR (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
            ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨∅, woodinSourceIndex θ⟩ₖ))) α := by
  let Q := (forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ
  let π := definableGraph Q (fun _ : V ↦ (∅ : V)) (by definability)
  have hπ : π ∈ A.P ^ Q := by
    rw [hP]
    exact definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ _ ↦ by simp)
  have hs := woodinSparseSourceStageCode_valid hΩ hAC hθ
  have hz : (∅ : V) ∈ succ (woodinSourceIndex θ) :=
    mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (empty_subset _))
  have hρ := (hs.system.projection hz (mem_succ_self _) (empty_subset _)).maps
  rw [(woodinSparseSourceStageCode_seed (θ := θ)).1, ← hP,
    (woodinSparseSourceStageCode_row (mem_succ_self θ)).1] at hρ
  rw [(woodinSparseSourceStageCode_row (mem_succ_self θ)).1,
    (woodinSparseSourceStageCode_row (mem_succ_self θ)).2]
  apply A.projectionQuotient_equivalence_directedClosedBelow_check A (Equiv.refl _)
    (fun _ _ ↦ Iff.rfl) (fun _ ↦ rfl) hπ hρ
    (woodinSparseRealizationMap_projection hΩ hAC hθ).maps
    (woodinSparseRealizationInverse_maps hΩ hAC hθ)
    (fun p hp ↦ ?_) (fun _ hq ↦ woodinSparseRealizationMap_right_inverse hΩ hAC hθ hq)
    (fun _ hp _ hq ↦ (woodinSparseRealizationMap_order_iff hΩ hAC hθ hp hq).symm)
  · exact A.woodinRaw_seed_directedClosedBelow_zf hΩ hAC hθ hP hR ho hπ
  · have h1 := function_value_mem hρ
      (function_value_mem (woodinSparseRealizationMap_projection hΩ hAC hθ).maps hp)
    have h2 := function_value_mem hπ hp
    rw [hP] at h1 h2
    rw [mem_singleton_iff.mp h1, mem_singleton_iff.mp h2]
/-- All completed source prefixes, including the inserted seed, have directed
bounds below their actual source cutoff. The final completed row is allowed. -/
theorem ForcingContext.woodinSparseSource_all_quotient_directedClosedBelow_zf
    (A : ForcingContext V) {Ω θ j : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hj : j ∈ succ (woodinSourceIndex θ))
    (hP : A.P = (forcingCodeP (woodinSparseSourceStageCode θ)) ‘ j)
    (hR : A.R = (forcingCodeR (woodinSparseSourceStageCode θ)) ‘ j) (ho : A.one = ∅) :
    ∀ α ∈ A.check ((woodinSparseSourceStageCardinals θ) ‘ j),
      IsForcingDirectedClosedAt
        (A.projectionQuotient ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
          ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨j, woodinSourceIndex θ⟩ₖ))
        (forcingSeparativeOrder
          (A.projectionQuotient ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
            ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨j, woodinSourceIndex θ⟩ₖ))
          (A.projectionQuotientOrder ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
            ((forcingCodeR (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
            ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨j, woodinSourceIndex θ⟩ₖ))) α := by
  rcases mem_succ_iff.mp hj with rfl | hj
  · intro α _
    have hs := woodinSparseSourceStageCode_valid hΩ hAC hθ
    rw [← hP, ← hR]
    apply A.identityQuotient_separative_directedClosedAt
    · rw [hP]
      exact (hs.system.projection (mem_succ_self _) (mem_succ_self _) (subset_refl _)).maps
    · intro p hp
      exact hs.system.split.projId (mem_succ_self _) (hP ▸ hp)
  · rcases woodinSourceIndex_cases hj with rfl | ⟨i, hi, rfl⟩
    · rw [(woodinSparseSourceStageCode_seed (θ := θ)).1] at hP
      rw [(woodinSparseSourceStageCode_seed (θ := θ)).2.1] at hR
      rw [woodinSparseSourceStageCardinals, woodinSourceCardinals_seed]
      exact A.woodinSparseSource_seed_directedClosedBelow_zf hΩ hAC hθ hP hR ho
    · let := IsOrdinal.of_mem hi
      have hi' := mem_succ_iff.mpr (Or.inr hi)
      have hisub : i ⊆ Ω := subset_trans (IsOrdinal.toIsTransitive.transitive _ hi) hθ
      rw [(woodinSparseSourceStageCode_row hi').1, (woodinSparseStage_old_row hi').1] at hP
      rw [(woodinSparseSourceStageCode_row hi').2, (woodinSparseStage_old_row hi').2] at hR
      have hP' : A.P = (forcingCodeP (woodinSparseSourceStageCode i)) ‘ (woodinSourceIndex i) := by
        rwa [(woodinSparseSourceStageCode_row (mem_succ_self i)).1]
      have hR' : A.R = (forcingCodeR (woodinSparseSourceStageCode i)) ‘ (woodinSourceIndex i) := by
        rwa [(woodinSparseSourceStageCode_row (mem_succ_self i)).2]
      rw [woodinSparseSourceStageCardinals_value hΩ hAC hθ hi',
        ← woodinSparseSourceStageCardinals_value hΩ hAC hisub (mem_succ_self i)]
      exact A.woodinSparseSource_quotient_directedClosedBelow_zf hΩ hAC hθ hi hP' hR' ho


end ZFVP

