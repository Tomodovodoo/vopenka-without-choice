import ZFVP.SetTheory.WoodinSupercompactHighCritical
import ZFVP.ModelTheory.SuccessorRankInaccessible

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSupercompact.no_rank_cofinalMap {δ X g : V} (hδ : IsWoodinSupercompact δ)
    (hX : X ∈ hierarchy δ) : ¬IsCofinalMap δ X g := by
  let := hδ.1.1
  intro hg
  let η := δ ∪ rank g
  let : IsOrdinal η := ordinal_union_ordinal δ (rank g)
  obtain ⟨γ, hηγ, hγ⟩ := sigmaOneStarCorrect_unbounded η
  let := hγ.1.ordinal
  have hδγ : δ ∈ γ := ordinal_mem_of_subset_mem
    (show δ ⊆ η from fun z hz ↦ mem_union_iff.mpr (Or.inl hz)) hηγ
  have hgγ : g ∈ hierarchy γ := (mem_hierarchy_iff_rank_mem _ _).mpr (ordinal_mem_of_subset_mem
    (show rank g ⊆ η from fun z hz ↦ mem_union_iff.mpr (Or.inr hz)) hηγ)
  have hrX := (mem_hierarchy_iff_rank_mem X δ).mp hX
  obtain ⟨_, ρ, _, hρ, u, hu, e, he, c, hc, hec, hue, hrXc⟩ :=
    hδ.highCritical.2.2 γ hδγ hγ g hgγ (rank X) hrX
  let := hρ.1.ordinal
  let := hc.ordinal
  let := hierarchy_transitive (succ ρ)
  let := hierarchy_transitive (succ γ)
  have hcρ := successorRankEmbedding_criticalPoint_lt_height he hc (hec.symm ▸ hδγ)
  have hXc : X ∈ hierarchy c := (mem_hierarchy_iff_rank_mem _ _).mpr hrXc
  have hXρ := hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hcρ) X hXc
  have heX := successorRankEmbedding_fixed_below_criticalPoint hρ.1 hγ.1 he hc hcρ X hXc
  have hinc : hierarchy ρ ⊆ hierarchy (succ ρ) := hierarchy_mono
    (by intro z hz; exact mem_succ_iff.mpr (Or.inr hz))
  have hucof : IsCofinalMap c X u := by
    apply (he.bounded_defined_iff boundedCofinalMapFormula_bounded
      (fun v ↦ IsCofinalMap (v 0) (v 1) (v 2)) ![c, X, u]
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hc.mem_domain, hinc X hXρ, hinc u hu])).mpr
    simpa [hec, heX, hue] using hg
  exact successorRankEmbedding_criticalPoint_no_rank_cofinalMap hρ.1 hγ.1 he hc hcρ hXc hucof

theorem IsWoodinSupercompact.inaccessible {δ : V} (hδ : IsWoodinSupercompact δ) :
    IsChoicelessInaccessible δ := by
  let := hδ.1.1
  exact ⟨hδ.1.1, hδ.omega_lt, fun α hα _ ↦ hδ.no_rank_cofinalMap (hierarchy_mem hα)⟩

theorem IsWoodinSupercompact.regular {δ : V} (hδ : IsWoodinSupercompact δ) : IsRegularCardinal δ := by
  let := hδ.1.1
  refine ⟨hδ.1, IsOrdinal.toIsTransitive.transitive _ hδ.omega_lt, ?_⟩
  rcases IsOrdinal.subset_iff.mp (internalCofinality_subset δ) with he | hlt
  · exact he
  · obtain ⟨g, hg⟩ := cofinalMap_exists δ
    exact False.elim (hδ.no_rank_cofinalMap (ordinal_mem_hierarchy_iff.mpr hlt) hg)

end ZFVP
