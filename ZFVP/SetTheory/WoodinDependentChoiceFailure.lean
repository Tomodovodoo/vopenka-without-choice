import ZFVP.ModelTheory.SuccessorRankDependentChoice
import ZFVP.SetTheory.DependentChoiceCofinality

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSupercompact.dependentChoiceFailure_below {δ κ : V} [IsOrdinal κ]
    (hδ : IsWoodinSupercompact δ) (hfail : ¬InternalDependentChoiceAt κ) :
    ∃ μ ∈ δ, ¬InternalDependentChoiceAt μ := by
  let := hδ.1.1
  let η := δ ∪ κ
  let : IsOrdinal η := ordinal_union_ordinal δ κ
  obtain ⟨γ, hηγ, hγ⟩ := sigmaOneStarCorrect_unbounded η
  let := hγ.1.ordinal
  have hδγ : δ ∈ γ := ordinal_mem_of_subset_mem
    (show δ ⊆ η from fun z hz ↦ mem_union_iff.mpr (Or.inl hz)) hηγ
  have hκγ : κ ∈ γ := ordinal_mem_of_subset_mem
    (show κ ⊆ η from fun z hz ↦ mem_union_iff.mpr (Or.inr hz)) hηγ
  obtain ⟨_, ρ, hρδ, hρ, μ, hμ, e, he, _c, _hc, _hec, heμ⟩ :=
    hδ.2 γ hδγ hγ κ (ordinal_mem_hierarchy_iff.mpr hκγ)
  let := hρ.1.ordinal
  let := hierarchy_transitive (succ ρ)
  let := hierarchy_transitive (succ γ)
  have hμord : IsOrdinal μ := by
    have hμs : μ ∈ hierarchy (succ ρ) := hierarchy_mono
      (by intro z hz; exact mem_succ_iff.mpr (Or.inr hz)) μ hμ
    apply (he.bounded_defined_iff isOrdinalFormula_bounded (fun v ↦ IsOrdinal (v 0))
      ![μ] (by simpa using hμs)).mpr
    simpa [heμ] using (inferInstance : IsOrdinal κ)
  let := hμord
  have hμρ : μ ∈ ρ := ordinal_mem_hierarchy_iff.mp hμ
  refine ⟨μ, IsOrdinal.toIsTransitive.mem_trans hμρ hρδ, ?_⟩
  intro hDC
  have ht := (successorRankEmbedding_dependentChoice_iff hδ hρ hγ he hμρ).mp hDC
  exact hfail (heμ ▸ ht)

theorem IsWoodinSupercompact.internalChoice_of_dependentChoiceBelow {δ : V}
    (hδ : IsWoodinSupercompact δ) (hDC : ∀ κ ∈ δ, InternalDependentChoiceAt κ) : InternalChoice V := by
  apply internalChoice_of_all_dependentChoiceAt
  intro κ hκ
  let := hκ
  by_contra hn
  obtain ⟨μ, hμ, hm⟩ := hδ.dependentChoiceFailure_below hn
  exact hm (hDC μ hμ)

theorem IsLeastDependentChoiceFailure.lt_supercompact {δ κ : V}
    (hκ : IsLeastDependentChoiceFailure κ) (hδ : IsWoodinSupercompact δ) : κ ∈ δ := by
  let := hκ.1
  let := hδ.1.1
  obtain ⟨μ, hμδ, hμ⟩ := hδ.dependentChoiceFailure_below hκ.2.1
  let := IsOrdinal.of_mem hμδ
  exact ordinal_mem_of_subset_mem (hκ.2.2 μ inferInstance hμ) hμδ

theorem IsWoodinSupercompact.initial_dependentChoice_failure {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    ∃ κ ∈ δ, IsLeastDependentChoiceFailure κ ∧ IsRegularCardinal κ ∧
      (∀ η ∈ κ, InternalDependentChoiceAt η) ∧ ¬InternalDependentChoiceAt κ := by
  obtain ⟨κ, hκ, _⟩ := leastDependentChoiceFailure_existsUnique hAC
  exact ⟨κ, hκ.lt_supercompact hδ, hκ, hκ.regular, fun η hη ↦ hκ.below hη, hκ.2.1⟩

theorem IsWoodinSupercompact.internalChoice_iff_dependentChoiceBelow {δ : V}
    (hδ : IsWoodinSupercompact δ) : InternalChoice V ↔ ∀ κ ∈ δ, InternalDependentChoiceAt κ := by
  constructor
  · intro hAC κ hκ
    let := hδ.1.1
    let := IsOrdinal.of_mem hκ
    exact dependentChoiceAt_of_internalChoice hAC κ
  · exact hδ.internalChoice_of_dependentChoiceBelow

end ZFVP
