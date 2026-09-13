import ZFVP.ModelTheory.WoodinSparseMarkedRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal θ]

theorem woodinSparseStageCode_initial_own_bound
    (hΩ : IsWoodinSupercompact Ω) :
    (forcingCodeP (woodinSparseStageCode (∅ : V))) ‘ ∅ ⊆
      hierarchy ((kpair.π₂ (woodinIterationRec (∅ : V))) ‘ ∅) := by
  rw [(woodinSparseStageCode_initial).1]
  simpa only [woodinIterationRec_initial, kpair.π₂_kpair, woodinInitialCardinals, forcingFamilyNext_new,
    woodinInitialStage, woodinSuccessorStep, woodinSuccessorAt, woodinStageCardinal_code,
    woodinSeedStage, woodinStagePoset_code, woodinStageOrder_code, woodinStageTop_code] using
    woodinSparseInitial_subset_hierarchy hΩ

theorem woodinSparseStageCode_successor_own_bound {k : V} [IsOrdinal k]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : succ k ∈ Ω) :
    (forcingCodeP (woodinSparseStageCode (succ k))) ‘ (succ k) ⊆
      hierarchy ((kpair.π₂ (woodinIterationRec (succ k))) ‘ (succ k)) := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hk
  have hkΩ := hsub k (mem_succ_self k)
  have ih := fun i hi ↦ woodinSparseRecodingRec_correct hΩ hAC i (hsub i hi)
  have hm := woodinSparseHistory_family hΩ hAC hsub ih
  have hd := (woodinNormalizedSuccessorCutoff_bounds hΩ hAC hkΩ).1
  have hQ : (woodinRecodingCarriers (woodinSparseRecodingHistory (succ k))) ‘ k ∈
      hierarchy (woodinNormalizedSuccessorCutoff k) := by
    apply woodinSparseHistory_small ih (mem_succ_self k) hd
    rw [woodinNormalizedSuccessorCutoff_actualCardinal hΩ hAC hkΩ]
    exact woodinIterationActualCardinal_increasing hΩ hAC hk (mem_succ_self k)
  rw [(woodinSparseStageCode_successor k).1, ← woodinNormalizedSuccessorCutoff_actualCardinal hΩ hAC hkΩ]
  exact woodinSparseSuccessorCarrier_subset_hierarchy hΩ hAC hkΩ hm
    (fun _ hi ↦ woodinSparseHistory_preorder ih hi)
    (woodinSparseRecodingHistory_tables (succ k)).1 (woodinSparseRecodingHistory_tables (succ k)).2.1 hQ

theorem woodinSparseStageCode_inverse_own_bound
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    (forcingCodeP (woodinSparseStageCode θ)) ‘ θ ⊆
      hierarchy ((kpair.π₂ (woodinIterationRec θ)) ‘ θ) := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have ih := fun i hi ↦ woodinSparseRecodingRec_correct hΩ hAC i (hsub i hi)
  have hm := woodinSparseHistory_family hΩ hAC hsub ih
  obtain ⟨_, hd, _, _⟩ := woodinNormalizedInverseCutoff_bounds hΩ hAC hθ h0 hlim hn
  have hQ : ∀ i ∈ θ, (woodinRecodingCarriers (woodinSparseRecodingHistory θ)) ‘ i ∈
      hierarchy (woodinNormalizedInverseCutoff θ) := by
    intro i hi
    apply woodinSparseHistory_small ih hi hd
    rw [woodinNormalizedInverseCutoff_actualCardinal hΩ hAC hsub h0 hlim hn]
    exact woodinIterationActualCardinal_increasing hΩ hAC hθ hi
  rw [(woodinSparseStageCode_inverse h0 hlim hn).1,
    ← woodinNormalizedInverseCutoff_actualCardinal hΩ hAC hsub h0 hlim hn]
  exact woodinSparseCompletedInverseCarrier_subset_hierarchy hΩ hAC hθ h0 hlim hn hm
    (fun _ hi ↦ woodinSparseHistory_preorder ih hi)
    (woodinSparseRecodingHistory_tables θ).1 (woodinSparseRecodingHistory_tables θ).2.1
    (fun _ hi _ hp ↦ woodinSparseHistory_sparse ih hi hp)
    (fun i hi j hj hij p hp ↦ by
      let := IsOrdinal.of_mem hj
      exact woodinSparseHistory_projection hΩ hAC hsub ih hi hj (IsOrdinal.toIsTransitive.transitive _ hij) hp)
    (fun _ hi ↦ woodinSparseHistory_top hΩ hAC hsub ih hi) hQ

theorem woodinSparseStageCode_direct_own_bound
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    (forcingCodeP (woodinSparseStageCode θ)) ‘ θ ⊆
      hierarchy ((kpair.π₂ (woodinIterationRec θ)) ‘ θ) := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hl := ordinal_limit_of_not_successor hlim
  have hcard := woodinDirect_stage_cardinal hΩ hAC hθ h0 hlim hinac
  have hpref := woodinIterationPrefix_of_stages (fun i hi ↦ ((woodinIterationExit hΩ hAC).2.1 i (hsub i hi)).1)
  have he := hpref.index_eq_regular_limit hl hinac.regular
  have hθinac : IsChoicelessInaccessible θ := he.symm ▸ hinac
  rw [hcard, (woodinSparseStageCode_direct h0 hlim hinac).1]
  apply woodinSparseDirectBase_subset_hierarchy_of_rows (woodinSparsePrefixCode_valid hΩ hAC hsub)
  intro i hi
  apply woodinSparsePrefixCode_small hΩ hAC hsub hi hθinac
  rw [← hcard]
  exact woodinIterationActualCardinal_increasing hΩ hAC hθ hi

theorem woodinSparseStageCode_own_bound
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    (forcingCodeP (woodinSparseStageCode θ)) ‘ θ ⊆
      hierarchy ((kpair.π₂ (woodinIterationRec θ)) ‘ θ) := by
  let := hΩ.inaccessible.1
  rcases IsOrdinal.subset_iff.mp hθ with he | hθ
  · subst Ω
    rw [woodinIteration_endpoint_cardinal hΩ hAC]
    exact woodinSparseStageCode_rows_subset_at_endpoint hΩ hAC θ (mem_succ_self θ)
  · by_cases hz : θ = ∅
    · subst θ
      exact woodinSparseStageCode_initial_own_bound hΩ
    · by_cases hs : θ = succ (⋃ˢ θ)
      · have hm : ⋃ˢ θ ∈ θ := (congrArg (fun z : V ↦ ⋃ˢ θ ∈ z) hs).mpr (mem_succ_self (⋃ˢ θ))
        let := IsOrdinal.of_mem hm
        have hh : succ (⋃ˢ θ) ∈ Ω := hs ▸ hθ
        simpa only [← hs] using woodinSparseStageCode_successor_own_bound hΩ hAC hh
      · by_cases hi : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))
        · exact woodinSparseStageCode_direct_own_bound hΩ hAC hθ hz hs hi
        · exact woodinSparseStageCode_inverse_own_bound hΩ hAC hθ hz hs hi

end ZFVP


