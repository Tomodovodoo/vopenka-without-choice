import ZFVP.ModelTheory.SuccessorRankLiftAssignmentGraph
import ZFVP.ModelTheory.ForcingRetractionSequences

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace SuccessorRankLiftData
variable {A B : ForcingContext V} {δ ε e π : V} (L : SuccessorRankLiftData A B δ ε e)
  (hπ : IsForcingRetraction A.P A.R B.P B.R π)
  (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P) (hone : A.one = B.one)

include hG hone in
theorem graph_assignment_representative {n : V} (hn : n ∈ (ω : V)) {b : B.Model}
    (hb : b ∈ domain (L.graph hπ) ^ B.check n) :
    ∃ s : V, ∃ hs : s ∈ lowRankNameSet A.P δ ^ n,
      b = B.sequenceValue s
        (fun i hi ↦ (A.nameSequence_of_mem_function (A.lowRankNameSet_names δ) hs i hi).mono hπ.inclusion) := by
  let j := ForcingContext.retractionEmbedding A B hπ hG
  have hn' : A.check n ∈ (ω : A.Model) := (A.checkEmbedding.natural_iff n).mpr hn
  have hjn : j (A.check n) = B.check n := ForcingContext.retractionInclusion_check A B hπ hG hone n
  rw [L.graph_domain_eq_rank_image hπ hG, ← hjn] at hb
  change b ∈ j (hierarchy (A.check δ)) ^ j (A.check n) at hb
  rw [← j.map_finiteFunctionSet _ hn'] at hb
  obtain ⟨c, hc, rfl⟩ := j.endExtension _ b hb
  obtain ⟨s, hsN, hs, hsc⟩ := A.lowRankFiniteAssignment_representative L.source_correct L.poset_mem hn hc
  refine ⟨s, hs, ?_⟩
  rw [← hsc]
  exact ForcingContext.retractionInclusion_sequenceValue A B hπ hG hone s hsN

end SuccessorRankLiftData
end ZFVP
