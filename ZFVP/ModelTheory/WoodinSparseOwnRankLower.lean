import ZFVP.ModelTheory.SparseCollapseRank
import ZFVP.ModelTheory.WoodinSparseOwnRank
import ZFVP.ModelTheory.WoodinSparseOwnCutoffs

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSparseStageCode_initial_rank_lower {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) :
    ((kpair.π₂ (woodinIterationRec (∅ : V))) ‘ ∅) ⊆
      rank ((forcingCodeP (woodinSparseStageCode (∅ : V))) ‘ ∅) := by
  obtain ⟨hc, hp, hκ, _⟩ := woodinNormalizationInitial_inputs hΩ
  have hr := sparseNormalizedPrefix_rank_lower (a := succ (∅ : V))
    (singletonForcing_preorder ∅) (singletonForcing_top ∅) hc hp
    (fun p h ↦ by
      have he : p = (∅ : V) := by simpa using h
      subst p
      exact isSparseFunctionOn_empty _)
    (woodinSeedCardinal_omega_subset (1 : V) (by simp)) hκ
  rw [(woodinSparseStageCode_initial).1]
  simpa only [woodinIterationRec_initial, kpair.π₂_kpair, woodinInitialCardinals,
    forcingFamilyNext_new, woodinInitialStage, woodinSuccessorStep, woodinSuccessorAt,
    woodinStageCardinal_code, woodinSeedStage, woodinStagePoset_code,
    woodinStageOrder_code, woodinStageTop_code, woodinSparseInitialCarrier] using hr

theorem woodinSparseStageCode_successor_rank_lower {Ω k : V} [IsOrdinal k]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : succ k ∈ Ω) :
    ((kpair.π₂ (woodinIterationRec (succ k))) ‘ (succ k)) ⊆
      rank ((forcingCodeP (woodinSparseStageCode (succ k))) ‘ (succ k)) := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hk
  have hkΩ := hsub k (mem_succ_self k)
  have hf := woodinSparsePrefixCode_valid hΩ hAC hsub
  have ht := hf.system.tops.top k (mem_succ_self k)
  have he := woodinSparsePrefixCode_top hΩ hAC hsub (mem_succ_self k)
  rw [he] at ht
  have hd := ((woodinIterationExit hΩ hAC).2.1 (succ k) hk).1.inaccessible (succ k) (mem_succ_self _)
  have hκ := ((woodinIterationExit hΩ hAC).2.1 k hkΩ).1.inaccessible k (mem_succ_self _)
  let := hd.1
  let := hκ.1
  have hlt := woodinIterationActualCardinal_increasing hΩ hAC hk (mem_succ_self k)
  have hr := sparseNormalizedPrefix_rank_lower
    (hf.system.order.preorder k (mem_succ_self k)) ht hd
    (woodinSparsePrefixCode_small hΩ hAC hsub (mem_succ_self k) hd hlt)
    (a := woodinSourceIndex (succ k))
    (fun p hp ↦ by
      rw [woodinSourceIndex_successor]
      exact woodinSparsePrefixCode_sparse hΩ hAC hsub (mem_succ_self k) hp)
    (IsOrdinal.toIsTransitive.mem_trans (show (1 : V) ∈ (ω : V) by simp) hκ.2.1)
    (IsOrdinal.toIsTransitive.transitive _ hlt)
  rw [(woodinSparseStageCode_successor k).1]
  unfold woodinSparseSuccessorCarrier woodinSparseSuccessorPool
  dsimp only
  rw [woodinSparsePrefix_successor_cutoff hΩ hAC hkΩ, he]
  exact hr

theorem woodinSparseStageCode_inverse_rank_lower {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    ((kpair.π₂ (woodinIterationRec θ)) ‘ θ) ⊆
      rank ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ) := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hl := ordinal_limit_of_not_successor hlim
  have hf := woodinSparsePrefixCode_valid hΩ hAC hsub
  obtain ⟨hR, ht⟩ := woodinSparsePrefix_inverse_base_laws hΩ hAC hsub hz hl
  have hd := ((woodinIterationExit hΩ hAC).2.1 θ hθ).1.inaccessible θ (mem_succ_self _)
  have hs := woodinIterationPrefix_of_stages
    (fun i hi ↦ ((woodinIterationExit hΩ hAC).2.1 i (hsub i hi)).1)
  have h1 : (1 : V) ⊆ woodinLimitCardinal (woodinIterationCardinalPrefix θ) := by
    intro x hx
    have hx0 : x = (∅ : V) := by simpa only [one_def, zero_def, mem_singleton_iff] using hx
    subst x
    exact hs.index_subset_limit hl _ hz
  have hr := sparseNormalizedHartogs_rank_lower hR ht hd
    (woodinSparsePrefix_inverse_base_small hΩ hAC hθ h0 hlim hn)
    (fun _ hp ↦ ((mem_woodinSparseInverseBase_iff hf).mp hp).1)
    (woodinIterationLimitCardinal_lt_actual_of_inverse hΩ hAC hθ hn) h1
  rw [(woodinSparseStageCode_inverse h0 hlim hn).1]
  unfold woodinSparseCompletedInverseCarrier woodinSparseInversePool
  dsimp only
  rw [woodinSparsePrefix_inverse_cutoff hΩ hAC hsub h0 hlim hn]
  exact hr

end ZFVP
