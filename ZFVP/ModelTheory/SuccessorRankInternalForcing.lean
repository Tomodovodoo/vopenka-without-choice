import ZFVP.ModelTheory.SuccessorRankForcingTable
import ZFVP.ModelTheory.SuccessorRankNameDomain
import ZFVP.Syntax.InternalForcingTableUniqueness
import ZFVP.Syntax.InternalForcingTableBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem successorRankEmbedding_internalForces_iff {δ ε f P R D n φ b p : V}
    (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (he : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) f)
    (hP : P ∈ hierarchy δ) (hR : R ∈ hierarchy δ) (hD : D ⊆ hierarchy δ)
    (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ D ^ n) (hp : p ∈ P) :
    InternalForces P R D n φ b p ↔
      InternalForces (f ‘ P) (f ‘ R) (f ‘ D) (f ‘ n) (f ‘ φ) (f ‘ b) (f ‘ p) := by
  let := hδ.ordinal
  let := hε.ordinal
  let := hierarchy_transitive (succ δ)
  let := hierarchy_transitive (succ ε)
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff 0 δ).mp hδ).2.support
  let : IsSequenceSupport (hierarchy ε) := ((cn_successor_iff 0 ε).mp hε).2.support
  have hU : hierarchy δ ∈ hierarchy (succ δ) := by rw [hierarchy_succ, mem_power_iff]
  have hlow : hierarchy δ ⊆ hierarchy (succ δ) := (hierarchy_transitive (succ δ)).transitive _ hU
  have hnU : n ∈ hierarchy δ := IsCodingSupport.natural_mem hφ.context
  have hφU : φ ∈ hierarchy δ := membershipFormulaCode_formula_mem_support hφ
  have hbU := function_mem_sequenceSupport hD hφ.context hb
  have hpU := (hierarchy_transitive δ).mem_trans hp hP
  have hDs : D ∈ hierarchy (succ δ) := by simpa only [hierarchy_succ, mem_power_iff] using hD
  have hbi := he.value_function (hlow _ hbU) (hlow _ hnU) hDs hb
  have hpi := (he.value_mem_iff (hlow _ hpU) (hlow _ hP)).mpr hp
  have hcU : ⟨n, φ⟩ₖ ∈ hierarchy δ := IsCodingSupport.kpair_closed n hnU φ hφU
  have hci := (he.value_mem_iff (hlow _ hcU) (hlow _ hδ.membershipFormulaFamily_mem)).mpr hφ
  rw [he.value_pair (hlow _ hnU) (hlow _ hφU) (hlow _ hcU),
    successorRankEmbedding_value_membershipFamily hδ hε he] at hci
  have hφi : IsMembershipFormulaCode (f ‘ n) (f ‘ φ) := hci
  let T := internalForcingTruthTable P R D
  have hTs : T ∈ hierarchy (succ δ) := hδ.internalForcingTruthTable_mem_successor hP hD
  have ht := internalForcingTruthTable_correct P R D
  have hti := successorRankEmbedding_internalForcingTruthTable hδ hε he hP hR hD hTs ht
  let code := ⟨n, φ⟩ₖ
  let arg := ⟨b, p⟩ₖ
  have haU : arg ∈ hierarchy δ := IsCodingSupport.kpair_closed b hbU p hpU
  have hzU : ⟨code, arg⟩ₖ ∈ hierarchy δ := IsCodingSupport.kpair_closed _ hcU _ haU
  have heq : f ‘ ⟨code, arg⟩ₖ = ⟨⟨f ‘ n, f ‘ φ⟩ₖ, ⟨f ‘ b, f ‘ p⟩ₖ⟩ₖ := by
    rw [he.value_pair (hlow _ hcU) (hlow _ haU) (hlow _ hzU)]
    rw [show f ‘ code = ⟨f ‘ n, f ‘ φ⟩ₖ from he.value_pair (hlow _ hnU) (hlow _ hφU) (hlow _ hcU),
      show f ‘ arg = ⟨f ‘ b, f ‘ p⟩ₖ from he.value_pair (hlow _ hbU) (hlow _ hpU) (hlow _ haU)]
  have hl : ForcingTableHolds T n φ b p ↔ ForcingTableHolds (f ‘ T) (f ‘ n) (f ‘ φ) (f ‘ b) (f ‘ p) := by
    have hh := he.value_mem_iff (hlow _ hzU) hTs
    rw [heq] at hh
    exact hh.symm
  exact (ht.lookup hφ hb hp).symm.trans (hl.trans (hti.lookup hφi hbi hpi))

theorem successorRankEmbedding_lowInternalForces_iff {δ ε f P R n φ b p : V}
    (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (he : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) f)
    (hP : P ∈ hierarchy δ) (hR : R ∈ hierarchy δ)
    (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ lowRankNameSet P δ ^ n) (hp : p ∈ P) :
    InternalForces P R (lowRankNameSet P δ) n φ b p ↔
      InternalForces (f ‘ P) (f ‘ R) (lowRankNameSet (f ‘ P) ε) (f ‘ n) (f ‘ φ) (f ‘ b) (f ‘ p) := by
  simpa only [successorRankEmbedding_value_lowRankNameSet hδ hε he hP] using
    successorRankEmbedding_internalForces_iff hδ hε he hP hR (lowRankNameSet_subset P δ) hφ hb hp

end ZFVP
