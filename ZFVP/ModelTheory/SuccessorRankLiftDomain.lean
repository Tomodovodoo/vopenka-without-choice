import ZFVP.ModelTheory.SuccessorRankLiftGraph
import ZFVP.ModelTheory.ForcingLowRankNames

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SuccessorRankLiftData
variable {A B : ForcingContext V} {δ ε e π : V} (L : SuccessorRankLiftData A B δ ε e)
  (hπ : IsForcingRetraction A.P A.R B.P B.R π)
  (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P)

include hG in
theorem graph_domain_eq_rank_image :
    domain (L.graph hπ) = ForcingContext.retractionInclusion A B hπ hG (hierarchy (A.check δ)) := by
  let := L.source_correct.ordinal
  apply mem_ext
  intro x
  constructor
  · intro hx
    obtain ⟨τ, hτ, rfl⟩ := (L.graph_domain hπ x).mp hx
    exact (ForcingContext.retractionInclusion_mem_iff A B hπ hG _ _).mpr
      (A.ofName_mem_checked_hierarchy τ hτ)
  · intro hx
    obtain ⟨y, hy, rfl⟩ := ForcingContext.retractionInclusion_endExtension A B hπ hG _ x hx
    obtain ⟨τ, hτ, rfl⟩ := (A.mem_checked_hierarchy_iff_low_name L.source_correct L.poset_mem y).mp hy
    exact (L.graph_domain hπ _).mpr ⟨τ, hτ, rfl⟩

theorem imageName_mem_rank (τ : ForcingName A.P) (hτ : τ.val ∈ hierarchy δ) :
    B.ofName (L.imageName τ hτ) ∈ hierarchy (B.check ε) := by
  let := L.source_correct.ordinal
  let := L.target_correct.ordinal
  exact B.ofName_mem_checked_hierarchy (L.imageName τ hτ)
    (successorRankElementaryMap L.embedding ⟨τ.val, hτ⟩).property

include hG in
theorem graph_value_mem_rank {x : B.Model} (hx : x ∈ domain (L.graph hπ)) :
    (L.graph hπ) ‘ x ∈ hierarchy (B.check ε) := by
  obtain ⟨τ, hτ, rfl⟩ := (L.graph_domain hπ x).mp hx
  rw [L.graph_value hπ hG]
  exact L.imageName_mem_rank τ hτ

include hG in
theorem graph_rank_function : L.graph hπ ∈ hierarchy (B.check ε) ^
    ForcingContext.retractionInclusion A B hπ hG (hierarchy (A.check δ)) := by
  let := L.graph_isFunction hπ hG
  rw [← L.graph_domain_eq_rank_image hπ hG]
  apply mem_function_of_mem_function_of_subset (IsFunction.mem_function _)
  intro y hy
  obtain ⟨x, hx⟩ := mem_range_iff.mp hy
  exact (value_eq_of_kpair_mem hx) ▸ L.graph_value_mem_rank hπ hG (mem_domain_of_kpair_mem hx)
end SuccessorRankLiftData
end ZFVP
