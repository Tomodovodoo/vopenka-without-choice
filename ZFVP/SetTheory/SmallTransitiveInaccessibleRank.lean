import ZFVP.SetTheory.ClosedRankStages
import ZFVP.SetTheory.RegularCofinalSurjection
import ZFVP.SetTheory.ChoicelessInaccessibleRank

/-! Transitive surjective images of small-rank sets stay below an inaccessible. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsChoicelessInaccessible.transitive_mem_of_surjection {κ C D f : V}
    (hκ : IsChoicelessInaccessible κ) (hC : IsTransitive C)
    (hD : D ∈ hierarchy κ) (hf : f ∈ C ^ D) (hfr : range f = C) :
    C ∈ hierarchy κ := by
  let := hκ.1
  by_contra hnot
  have hκr : κ ⊆ rank C := by
    rcases IsOrdinal.mem_trichotomy κ (rank C) with h | h | h
    · exact IsOrdinal.toIsTransitive.transitive _ h
    · exact h ▸ subset_refl _
    · exact (hnot ((mem_hierarchy_iff_rank_mem _ _).mpr h)).elim
  let g := definableGraph C (rank : V → V) inferInstance
  have hg : g ∈ (rank C) ^ C :=
    definableGraph_mem_function_of_mapsTo C (rank C) rank inferInstance (fun _ hx ↦ rank_mem hx)
  have hgr : range g = rank C := by
    apply subset_antisymm (range_subset_of_mem_function hg)
    intro α hα
    obtain ⟨x, hx, hrx⟩ := exists_mem_rank_eq hC hα
    apply mem_range_of_kpair_mem
    exact (pair_mem_definableGraph_iff C rank inferInstance x α).mpr ⟨hx, hrx.symm⟩
  obtain ⟨r, hr, hrr⟩ := surjection_of_injection (cardLE_of_subset hκr) ⟨ω, hκ.2.1⟩
  have hfg := compose_function hf hg
  have hfgr := range_compose_surjective hf hg hfr hgr
  have hall := compose_function hfg hr
  have hallr := range_compose_surjective hfg hr hfgr hrr
  exact hκ.no_rank_cofinalMap hD
    (cofinalMap_precompose_surjection (identity_isCofinalMap κ) hall hallr)

theorem IsChoicelessInaccessible.transitive_mem_of_cardLE {κ C D : V}
    (hκ : IsChoicelessInaccessible κ) (hC : IsTransitive C)
    (hD : D ∈ hierarchy κ) (hcard : C ≤# D) : C ∈ hierarchy κ := by
  let := hκ.1
  by_cases hne : IsNonempty C
  · obtain ⟨f, hf, hfr⟩ := surjection_of_injection hcard hne
    exact hκ.transitive_mem_of_surjection hC hD hf hfr
  · have hzero : C = ∅ := by
      apply mem_ext
      intro x
      constructor
      · intro hx
        exact (hne ⟨x, hx⟩).elim
      · simp
    rw [hzero]
    exact (hierarchy_transitive κ).mem_trans (show (∅ : V) ∈ ω by simp)
      (ordinal_mem_hierarchy_iff.mpr hκ.2.1)

end ZFVP
