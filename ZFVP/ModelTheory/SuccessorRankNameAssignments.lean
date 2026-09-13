import ZFVP.ModelTheory.SuccessorRankNameDomain
import ZFVP.ModelTheory.EmbeddingOmegaFixation
import ZFVP.ModelTheory.EmbeddingAssignments
import ZFVP.SetTheory.FiniteCodingClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem successorRankEmbedding_nameAssignment {δ ε e P n b : V}
    (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (he : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) e)
    (hP : P ∈ hierarchy δ) (hn : n ∈ (ω : V)) (hb : b ∈ lowRankNameSet P δ ^ n) :
    e ‘ b ∈ lowRankNameSet (e ‘ P) ε ^ n ∧ ∀ i ∈ n, (e ‘ b) ‘ i = e ‘ (b ‘ i) := by
  let := hδ.ordinal
  let := hε.ordinal
  let := hierarchy_transitive (succ δ)
  let := hierarchy_transitive (succ ε)
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff 0 δ).mp hδ).2.support
  have hU : hierarchy δ ∈ hierarchy (succ δ) := by rw [hierarchy_succ, mem_power_iff]
  have hlow : hierarchy δ ⊆ hierarchy (succ δ) := (hierarchy_transitive (succ δ)).transitive _ hU
  have hω := hlow _ (IsCodingSupport.omega_mem (U := hierarchy δ))
  have hbU := function_mem_sequenceSupport (lowRankNameSet_subset P δ) hn hb
  have hnU : n ∈ hierarchy δ := IsCodingSupport.natural_mem hn
  have hD : lowRankNameSet P δ ∈ hierarchy (succ δ) := by
    simpa only [hierarchy_succ, mem_power_iff] using lowRankNameSet_subset P δ
  constructor
  · have hh := he.value_function (hlow _ hbU) (hlow _ hnU) hD hb
    rwa [successorRankEmbedding_value_lowRankNameSet hδ hε he hP, he.value_natural_of_omega_mem hω hn] at hh
  · intro i hi
    have hh := he.value_apply (hlow _ hbU) (hlow _ hnU) (IsFunction.of_mem hb) (domain_eq_of_mem_function hb) hi
    rwa [he.value_natural_of_omega_mem hω (IsOrdinal.toIsTransitive.mem_trans hi hn)] at hh

end ZFVP
