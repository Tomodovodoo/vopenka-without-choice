import ZFVP.SetTheory.TwoStepForcing
import ZFVP.SetTheory.ForcingUniqueNameRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem twoStepNames_mem_hierarchy_limit {Q t θ : V} [IsOrdinal θ]
    (hs : ∀ α ∈ θ, succ α ∈ θ) (hQ : Q ∈ hierarchy θ) (ht : t ∈ hierarchy θ) :
    twoStepNames Q t ∈ hierarchy θ := by
  obtain ⟨α, hα, hQα, htα⟩ := common_hierarchy_stage hs hQ ht
  let := IsOrdinal.of_mem hα
  apply subset_mem_hierarchy_limit hs (hierarchy_mem hα)
  intro z hz
  rcases mem_union_iff.mp hz with hz | hz
  · exact transitive_subnameClosed (hierarchy_transitive α) Q hQα z hz
  · exact (mem_singleton_iff.mp hz).symm ▸ htα

theorem twoStepConditions_mem_hierarchy_limit {P R Q t θ : V} [IsOrdinal θ]
    (hs : ∀ α ∈ θ, succ α ∈ θ) (hP : P ∈ hierarchy θ)
    (hQ : Q ∈ hierarchy θ) (ht : t ∈ hierarchy θ) :
    twoStepConditions P R Q t ∈ hierarchy θ := by
  apply subset_mem_hierarchy_limit hs
    (prod_mem_hierarchy_limit hs hP (twoStepNames_mem_hierarchy_limit hs hQ ht))
  exact sep_subset

theorem twoStepOrder_mem_hierarchy_limit {P R Q S t θ : V} [IsOrdinal θ]
    (hs : ∀ α ∈ θ, succ α ∈ θ) (hP : P ∈ hierarchy θ)
    (hQ : Q ∈ hierarchy θ) (ht : t ∈ hierarchy θ) :
    twoStepOrder P R Q S t ∈ hierarchy θ := by
  have hc := twoStepConditions_mem_hierarchy_limit (R := R) hs hP hQ ht
  apply subset_mem_hierarchy_limit hs (prod_mem_hierarchy_limit hs hc hc)
  intro z hz
  unfold twoStepOrder at hz
  exact (mem_sep_iff.mp hz).1

end ZFVP
