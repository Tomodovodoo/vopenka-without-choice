import ZFVP.ModelTheory.FiniteRankLift
import ZFVP.ModelTheory.EmbeddingAssignments

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace FiniteRankLiftData
variable {A B : ForcingContext V} {δ ε e : V} (L : FiniteRankLiftData A B δ ε e)
include L

theorem nameAssignment {n b : V} (hn : n ∈ (ω : V)) (hb : b ∈ lowRankNameSet A.P δ ^ n) :
    e ‘ b ∈ lowRankNameSet B.P ε ^ n ∧ ∀ i ∈ n, (e ‘ b) ‘ i = e ‘ (b ‘ i) := by
  let := L.source_inaccessible.1
  let := L.target_inaccessible.1
  let := hierarchy_transitive (ordinalAdd ε (ω : V))
  let := hierarchy_isSequenceSupport L.source_inaccessible.2.1 L.source_inaccessible.rankCriterion.2.2.1
  let := hierarchy_isSequenceSupport
    (IsOrdinal.toIsTransitive.mem_trans L.source_inaccessible.2.1 (ordinalAdd_omega_gt δ))
    (fun _ ↦ ordinalAdd_omega_succ_closed δ)
  have hbA := L.low_mem_allowance (function_mem_sequenceSupport (lowRankNameSet_subset A.P δ) hn hb)
  have hnA : n ∈ hierarchy (ordinalAdd δ (ω : V)) := IsCodingSupport.natural_mem hn
  constructor
  · have hh := L.embedding.value_function hbA hnA
      (L.subset_mem_allowance (lowRankNameSet_subset A.P δ)) hb
    rwa [L.nameDomain_image, L.embedding.value_natural hn] at hh
  · intro i hi
    have hh := L.embedding.value_apply hbA hnA (IsFunction.of_mem hb) (domain_eq_of_mem_function hb) hi
    rwa [L.embedding.value_natural (IsOrdinal.toIsTransitive.mem_trans hi hn)] at hh

theorem image_assignment {n b : V} (hn : n ∈ (ω : V)) (hb : b ∈ lowRankNameSet A.P δ ^ n) :
    e ‘ b ∈ lowRankNameSet B.P ε ^ n := (L.nameAssignment hn hb).1
end FiniteRankLiftData
end ZFVP
