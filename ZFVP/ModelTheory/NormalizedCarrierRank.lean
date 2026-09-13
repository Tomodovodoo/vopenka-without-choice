import ZFVP.ModelTheory.NormalizedTwoStepComparison
import ZFVP.SetTheory.RankBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem normalizedNameTwoStep_mem_larger_hierarchy {P R one δ Q ξ : V} [IsOrdinal δ] [IsOrdinal ξ]
    (hξ : ∀ β ∈ ξ, succ β ∈ ξ) (hδξ : δ ∈ ξ) (hP : P ∈ hierarchy δ) :
    normalizedNameTwoStep P R one δ Q ∈ hierarchy ξ := by
  have hV : hierarchy δ ∈ hierarchy ξ := by
    rw [mem_hierarchy_iff_rank_mem, rank_hierarchy]
    exact hδξ
  have hpool : normalizedNamePool P R one δ Q ∈ hierarchy ξ :=
    subset_mem_hierarchy_limit hξ hV sep_subset
  exact prod_mem_hierarchy_limit hξ
    (hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hδξ) P hP) hpool

theorem nameTwoStepOrderOn_mem_hierarchy {P R S C ξ : V} [IsOrdinal ξ]
    (hξ : ∀ β ∈ ξ, succ β ∈ ξ) (hC : C ∈ hierarchy ξ) :
    nameTwoStepOrderOn P R S C ∈ hierarchy ξ :=
  subset_mem_hierarchy_limit hξ (prod_mem_hierarchy_limit hξ hC hC) sep_subset

end ZFVP
