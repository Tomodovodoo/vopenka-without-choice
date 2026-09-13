import ZFVP.ModelTheory.WoodinSparseOwnRank
import ZFVP.ModelTheory.WoodinSparseCodeCompatibility

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal θ]

theorem woodinIterationLimitCardinal_subset_actual
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω) :
    woodinLimitCardinal (woodinIterationCardinalPrefix θ) ⊆
      (kpair.π₂ (woodinIterationRec θ)) ‘ θ := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hs := woodinIterationPrefix_of_stages
    (fun i hi ↦ ((woodinIterationExit hΩ hAC).2.1 i (hsub i hi)).1)
  have hd := ((woodinIterationExit hΩ hAC).2.1 θ hθ).1.inaccessible θ (mem_succ_self θ)
  let := hd.1
  intro β hβ
  obtain ⟨i, hi, hβi⟩ := hs.limitCardinal_cofinal hβ
  rw [woodinIterationCardinalPrefix_value hΩ hAC hsub hi] at hβi
  exact IsOrdinal.toIsTransitive.mem_trans hβi (woodinIterationActualCardinal_increasing hΩ hAC hθ hi)

theorem woodinIterationLimitCardinal_lt_actual_of_inverse
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    woodinLimitCardinal (woodinIterationCardinalPrefix θ) ∈
      (kpair.π₂ (woodinIterationRec θ)) ‘ θ := by
  let := hΩ.inaccessible.1
  have hs := woodinIterationPrefix_of_stages
    (fun i hi ↦ ((woodinIterationExit hΩ hAC).2.1 i (IsOrdinal.toIsTransitive.mem_trans hi hθ)).1)
  let := hs.limitCardinal_ordinal
  have hd := ((woodinIterationExit hΩ hAC).2.1 θ hθ).1.inaccessible θ (mem_succ_self θ)
  let := hd.1
  rcases IsOrdinal.subset_iff.mp (woodinIterationLimitCardinal_subset_actual hΩ hAC hθ) with he | he
  · exact False.elim (hn (he.symm ▸ hd))
  · exact he

theorem woodinSparsePrefix_successor_cutoff {k : V} [IsOrdinal k]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : k ∈ Ω) :
    woodinPrefixCutoff ((forcingCodeP (woodinSparsePrefixCode (succ k))) ‘ k)
      ((forcingCodeR (woodinSparsePrefixCode (succ k))) ‘ k)
      ((forcingCodet (woodinSparsePrefixCode (succ k))) ‘ k)
      ((kpair.π₂ (woodinIterationRec k)) ‘ k) =
        (kpair.π₂ (woodinIterationRec (succ k))) ‘ (succ k) := by
  let := hΩ.inaccessible.1
  have hsub : succ k ⊆ Ω := by
    intro i hi
    rcases mem_succ_iff.mp hi with he | hi
    · exact he ▸ hk
    · exact IsOrdinal.toIsTransitive.mem_trans hi hk
  have ih := fun i hi ↦ woodinSparseRecodingRec_correct hΩ hAC i (hsub i hi)
  have he := woodinRecodedSuccessorCutoff_eq hΩ hAC hk
    (woodinSparseHistory_family hΩ hAC hsub ih) (fun _ hi ↦ woodinSparseHistory_preorder ih hi)
    (woodinSparseRecodingHistory_tables (succ k)).1 (woodinSparseRecodingHistory_tables (succ k)).2.1
  change woodinNormalizedSuccessorCutoff k = woodinPrefixCutoff
    ((forcingCodeP (woodinSparsePrefixCode (succ k))) ‘ k)
    ((forcingCodeR (woodinSparsePrefixCode (succ k))) ‘ k)
    ((forcingCodet (woodinSparsePrefixCode (succ k))) ‘ k)
    ((kpair.π₂ (woodinIterationRec k)) ‘ k) at he
  exact he.symm.trans (woodinNormalizedSuccessorCutoff_actualCardinal hΩ hAC hk)

theorem woodinSparsePrefix_inverse_cutoff
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    woodinSparseInverseCutoff θ (woodinSparsePrefixCode θ) =
      (kpair.π₂ (woodinIterationRec θ)) ‘ θ := by
  have ih := fun i hi ↦ woodinSparseRecodingRec_correct hΩ hAC i (hθ i hi)
  have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have he := woodinSparseInverseCutoff_eq hΩ hAC hθ
    (woodinSparseHistory_family hΩ hAC hθ ih) (fun _ hi ↦ woodinSparseHistory_preorder ih hi)
    (woodinSparseRecodingHistory_tables θ).1 (woodinSparseRecodingHistory_tables θ).2.1
    hz (ordinal_limit_of_not_successor hlim)
    (fun _ hi _ hp ↦ woodinSparseHistory_sparse ih hi hp)
    (fun i hi j hj hij p hp ↦ by
      let := IsOrdinal.of_mem hj
      exact woodinSparseHistory_projection hΩ hAC hθ ih hi hj (IsOrdinal.toIsTransitive.transitive _ hij) hp)
    (fun _ hi ↦ woodinSparseHistory_top hΩ hAC hθ ih hi)
  exact he.symm.trans (woodinNormalizedInverseCutoff_actualCardinal hΩ hAC hθ h0 hlim hn)

theorem woodinSparsePrefix_inverse_base_laws
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : (∅ : V) ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ) :
    IsForcingPreorder (woodinSparseInverseBase θ (woodinSparsePrefixCode θ))
      (woodinSparseInverseOrder θ (woodinSparsePrefixCode θ)) ∧
    IsForcingTop (woodinSparseInverseBase θ (woodinSparsePrefixCode θ))
      (woodinSparseInverseOrder θ (woodinSparsePrefixCode θ)) ∅ := by
  have ih := fun i hi ↦ woodinSparseRecodingRec_correct hΩ hAC i (hθ i hi)
  exact woodinSparseInverseBase_recoded_laws hΩ hAC hθ
    (woodinSparseHistory_family hΩ hAC hθ ih) (fun _ hi ↦ woodinSparseHistory_preorder ih hi)
    (woodinSparseRecodingHistory_tables θ).1 (woodinSparseRecodingHistory_tables θ).2.1 h0 hlim
    (fun _ hi _ hp ↦ woodinSparseHistory_sparse ih hi hp)
    (fun i hi j hj hij p hp ↦ by
      let := IsOrdinal.of_mem hj
      exact woodinSparseHistory_projection hΩ hAC hθ ih hi hj (IsOrdinal.toIsTransitive.transitive _ hij) hp)
    (fun _ hi ↦ woodinSparseHistory_top hΩ hAC hθ ih hi)

theorem woodinSparsePrefix_inverse_base_small
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    woodinSparseInverseBase θ (woodinSparsePrefixCode θ) ∈
      hierarchy ((kpair.π₂ (woodinIterationRec θ)) ‘ θ) := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  obtain ⟨_, hd, hθd, _⟩ := woodinNormalizedInverseCutoff_bounds hΩ hAC hθ h0 hlim hn
  rw [← woodinNormalizedInverseCutoff_actualCardinal hΩ hAC hsub h0 hlim hn]
  let := hd.1
  apply woodinSparseInverseBase_small (woodinSparsePrefixCode_valid hΩ hAC hsub) hd
    (ordinal_mem_hierarchy_iff.mpr hθd)
  intro i hi
  apply woodinSparsePrefixCode_small hΩ hAC hsub hi hd
  rw [woodinNormalizedInverseCutoff_actualCardinal hΩ hAC hsub h0 hlim hn]
  exact woodinIterationActualCardinal_increasing hΩ hAC hθ hi

end ZFVP

