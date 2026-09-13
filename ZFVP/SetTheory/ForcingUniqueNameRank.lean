import ZFVP.SetTheory.ForcingUniqueName
import ZFVP.SetTheory.RankBounds
import ZFVP.SetTheory.CodingUniverse
import ZFVP.SetTheory.FormulaReflection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem nameClosure_mem_hierarchy_limit {δ τ : V} [IsOrdinal δ]
    (hs : ∀ α ∈ δ, succ α ∈ δ) (hτ : τ ∈ hierarchy δ) : nameClosure τ ∈ hierarchy δ := by
  have hr := (mem_hierarchy_iff_rank_mem τ δ).mp hτ
  have ht : τ ∈ hierarchy (succ (rank τ)) := by
    rw [hierarchy_succ, mem_power_iff]
    exact subset_hierarchy_rank τ
  exact subset_mem_hierarchy_limit hs (hierarchy_mem (hs _ hr))
    (nameClosure_minimal (transitive_subnameClosed (hierarchy_transitive _)) ht)

theorem forcingWitnessBound_le_of_witness {P a ν β : V} [IsOrdinal β]
    (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (hν : IsForcingName P ν)
    (hνβ : ν ∈ hierarchy β) (hf : ∀ p ∈ P, p ∈ F a ν) :
    forcingWitnessBound P F hF a ⊆ β := by
  exact (leastOrdinalOrZero_spec _ _ a (forcingWitnessBound_exists P F hF a)).2.2 β inferInstance
    (fun p hp _ ↦ ⟨ν, hνβ, hν, hf p hp⟩)

theorem forcingUniqueName_mem_hierarchy_of_witness {P R a ν δ : V} [IsOrdinal δ]
    (hs : ∀ α ∈ δ, succ α ∈ δ) (hP : P ∈ hierarchy δ)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (hν : IsForcingName P ν)
    (hνδ : ν ∈ hierarchy δ) (hf : ∀ p ∈ P, p ∈ F a ν) :
    forcingUniqueName P R F hF a ∈ hierarchy δ := by
  have hr := (mem_hierarchy_iff_rank_mem ν δ).mp hνδ
  have hνβ : ν ∈ hierarchy (succ (rank ν)) := by
    rw [hierarchy_succ, mem_power_iff]
    exact subset_hierarchy_rank ν
  have hle := forcingWitnessBound_le_of_witness F hF hν hνβ hf
  let β := forcingWitnessBound P F hF a
  let : IsOrdinal β := leastOrdinalOrZero_ordinal _ _ _
  have hβ : β ∈ δ := ordinal_mem_of_subset_mem hle (hs _ hr)
  have hE : forcingWitnessName P F hF a ∈ hierarchy δ :=
    subset_mem_hierarchy_limit hs (prod_mem_hierarchy_limit hs (hierarchy_mem hβ) hP) sep_subset
  have hC := nameClosure_mem_hierarchy_limit hs hE
  apply subset_mem_hierarchy_limit hs (prod_mem_hierarchy_limit hs hC hP)
  intro z hz
  unfold forcingUniqueName forcingUnionName at hz
  exact (mem_sep_iff.mp hz).1

end ZFVP
