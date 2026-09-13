import ZFVP.ModelTheory.ForcingWeaklyLSCardinal
import ZFVP.ModelTheory.ForcingLowRankAssignments
import ZFVP.ModelTheory.ForcingHierarchyCover
import ZFVP.SetTheory.LSCorrectLimits
import ZFVP.SetTheory.StrongLSWeakLS

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem lsInputNameEvaluation_range (A : ForcingContext V) (γ : V) [IsOrdinal γ] :
    range (A.evaluationGraph (forcingNameHierarchy A.P γ)
      (forcingNameHierarchy_names A.P γ)) = hierarchy (A.check γ) :=
  A.hierarchyEvaluation_range γ

/-- A smaller LS cardinal bounds all input names and conditions needed
to close the lifted hull under functions on a requested low rank. -/
theorem ls_small_input_bounds (A : ForcingContext V) {κ γ : V}
    (hκ : IsLSCardinal κ) (hcorrect : Cn 1 κ)
    (hcof : ∀ α ∈ κ, ∃ μ ∈ κ, α ∈ μ ∧ IsLSCardinal μ)
    (hP : A.P ∈ hierarchy κ) (hγ : γ ∈ κ) :
    ∃ δ ν : V, δ ∈ κ ∧ IsLSCardinal δ ∧ ν ∈ δ ∧
      γ ⊆ ν ∧ succ (ω : V) ⊆ ν ∧
      A.P ⊆ hierarchy ν ∧ forcingNameHierarchy A.P γ ⊆ hierarchy ν := by
  let := hκ.1.1
  let := IsOrdinal.of_mem hγ
  let B := forcingNameHierarchy A.P γ
  have hB : B ∈ hierarchy κ := hcorrect.forcingNameHierarchy_closed hP hγ
  have hrP : rank A.P ∈ κ := (mem_hierarchy_iff_rank_mem _ _).mp hP
  have hrB : rank B ∈ κ := (mem_hierarchy_iff_rank_mem _ _).mp hB
  have hsω : succ (ω : V) ∈ κ := hcorrect.successor_closed _ hκ.2.1
  let ν := (rank A.P ∪ rank B) ∪ (γ ∪ succ (ω : V))
  let := ordinal_union_ordinal (rank A.P) (rank B)
  let := ordinal_union_ordinal γ (succ (ω : V))
  let := ordinal_union_ordinal (rank A.P ∪ rank B) (γ ∪ succ (ω : V))
  have hν : ν ∈ κ := ordinal_union_mem (ordinal_union_mem hrP hrB) (ordinal_union_mem hγ hsω)
  obtain ⟨δ, hδ, hνδ, hLSδ⟩ := hcof ν hν
  have hleft : rank A.P ∪ rank B ⊆ ν := subset_union_left _ _
  have hright : γ ∪ succ (ω : V) ⊆ ν := subset_union_right _ _
  refine ⟨δ, ν, hδ, hLSδ, hνδ, subset_trans (subset_union_left _ _) hright,
    subset_trans (subset_union_right _ _) hright, ?_, ?_⟩
  · exact subset_trans (subset_hierarchy_rank A.P)
      (hierarchy_mono (subset_trans (subset_union_left _ _) hleft))
  · exact subset_trans (subset_hierarchy_rank B)
      (hierarchy_mono (subset_trans (subset_union_right _ _) hleft))

/-- The original unboundedness hypothesis supplies arbitrarily high
correct limits at which the forcing is rank-small. -/
theorem exists_rank_small_correct_ls_limit (A : ForcingContext V)
    (hLS : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsLSCardinal κ)
    (ξ : V) [IsOrdinal ξ] :
    ∃ κ : V, ξ ∈ κ ∧ IsLSCardinal κ ∧ Cn 1 κ ∧ A.P ∈ hierarchy κ ∧
      ∀ α ∈ κ, ∃ μ ∈ κ, α ∈ μ ∧ IsLSCardinal μ := by
  let := ordinal_union_ordinal ξ (rank A.P)
  obtain ⟨κ, hb, hκ, hc, hcof⟩ := lsCorrectLimit_unbounded hLS 1 (ξ ∪ rank A.P)
  let := hκ.1.1
  exact ⟨κ, ordinal_mem_of_subset_mem (subset_union_left _ _) hb, hκ, hc,
    (mem_hierarchy_iff_rank_mem _ _).mpr
      (ordinal_mem_of_subset_mem (subset_union_right _ _) hb), hcof⟩

end ForcingContext
end ZFVP
