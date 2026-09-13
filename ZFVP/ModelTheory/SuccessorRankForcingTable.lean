import ZFVP.ModelTheory.InternalForcingTableTransport
import ZFVP.ModelTheory.SuccessorRankSyntaxFamily
import ZFVP.SetTheory.AtomicTruthTableBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem successorRankEmbedding_internalForcingTruthTable {δ ε f P R D T : V}
    (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (he : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) f)
    (hP : P ∈ hierarchy δ) (hR : R ∈ hierarchy δ) (hD : D ⊆ hierarchy δ)
    (hT : T ∈ hierarchy (succ δ)) (ht : IsInternalForcingTruthTable P R D T) :
    IsInternalForcingTruthTable (f ‘ P) (f ‘ R) (f ‘ D) (f ‘ T) := by
  let := hδ.ordinal
  let := hε.ordinal
  let := hierarchy_transitive (succ δ)
  let := hierarchy_transitive (succ ε)
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff 0 δ).mp hδ).2.support
  let : IsSequenceSupport (hierarchy ε) := ((cn_successor_iff 0 ε).mp hε).2.support
  have hU : hierarchy δ ∈ hierarchy (succ δ) := by rw [hierarchy_succ, mem_power_iff]
  have hlow : hierarchy δ ⊆ hierarchy (succ δ) := (hierarchy_transitive (succ δ)).transitive _ hU
  have him : f ‘ (hierarchy δ) = hierarchy ε := successorRankEmbedding_value_hierarchy he
  let : IsSequenceSupport (f ‘ (hierarchy δ)) := him.symm ▸ (inferInstance : IsSequenceSupport (hierarchy ε))
  obtain ⟨H, hH, ha⟩ := hδ.exists_atomicTruthTable_mem_successor hP R
  have hDs : D ∈ hierarchy (succ δ) := by simpa only [hierarchy_succ, mem_power_iff] using hD
  exact he.value_internalForcingTruthTable hU (hlow _ IsCodingSupport.omega_mem)
    (hlow _ hδ.membershipFormulaFamily_mem) (successorRankEmbedding_value_membershipFamily hδ hε he)
    (hlow _ hP) (hlow _ hR) hDs hH hT ((hierarchy_transitive δ).transitive _ hP) hD ha ht

end ZFVP
