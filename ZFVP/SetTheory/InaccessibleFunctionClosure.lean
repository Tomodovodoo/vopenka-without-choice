import ZFVP.SetTheory.ChoicelessInaccessibleRank
import ZFVP.SetTheory.SigmaOneStarCorrectness
import ZFVP.SetTheory.FiniteCodingClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsChoicelessInaccessible.function_mem {δ X f : V} (hδ : IsChoicelessInaccessible δ)
    (hX : X ∈ hierarchy δ) (hf : f ∈ hierarchy δ ^ X) : f ∈ hierarchy δ := by
  let := hδ.1
  let := IsFunction.of_mem hf
  have hs : ∀ β ∈ δ, succ β ∈ δ := hδ.rankCriterion.2.2.1
  have hr : range f ∈ hierarchy δ := hδ.rankCriterion.2.2.2.range_mem hs hX hf
  apply subset_mem_hierarchy_limit hs (prod_mem_hierarchy_limit hs hX hr)
  have hdom : domain f = X := domain_eq_of_mem_function hf
  exact hdom ▸ subset_prod_of_mem_function (IsFunction.mem_function f)

theorem IsChoicelessInaccessible.rankFunctionClosed {δ α : V}
    (hδ : IsChoicelessInaccessible δ) (hα : α ∈ δ) : IsRankFunctionClosed α (hierarchy δ) := by
  let := hδ.1
  let := IsOrdinal.of_mem hα
  intro f hf
  exact hδ.function_mem (hierarchy_mem hα) hf

end ZFVP
