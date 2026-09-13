import ZFVP.Syntax.InternalForcingTruthTables
import ZFVP.Syntax.CodingSupportSyntax
import ZFVP.SetTheory.CnAbsoluteness

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internalForcingTruthTable_subset_support {U P R D : V} [IsSequenceSupport U]
    (hP : P ⊆ U) (hD : D ⊆ U) : internalForcingTruthTable P R D ⊆ U := by
  intro z hz
  have hs : z ∈ (formulaFamily membershipLanguageCode ∅ : V) ×ˢ (finiteSequences D ×ˢ P) :=
    (mem_sep_iff.mp hz).1
  obtain ⟨c, hc, w, hw, rfl⟩ := mem_prod_iff.mp hs
  obtain ⟨b, hb, p, hp, rfl⟩ := mem_prod_iff.mp hw
  exact IsCodingSupport.kpair_closed _ (membershipFormulaFamily_subset_support U c hc) _
    (IsCodingSupport.kpair_closed _ (finiteSequences_subset_support hD b hb) _ (hP p hp))

theorem Cn.internalForcingTruthTable_mem_successor {δ P R D : V} (hδ : Cn 1 δ)
    (hP : P ∈ hierarchy δ) (hD : D ⊆ hierarchy δ) :
    internalForcingTruthTable P R D ∈ hierarchy (succ δ) := by
  let := hδ.ordinal
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff 0 δ).mp hδ).2.support
  rw [hierarchy_succ, mem_power_iff]
  exact internalForcingTruthTable_subset_support ((hierarchy_transitive δ).transitive P hP) hD

theorem Cn.exists_internalForcingTruthTable {δ P R D : V} (hδ : Cn 1 δ)
    (hP : P ∈ hierarchy δ) (hD : D ⊆ hierarchy δ) :
    ∃ T ∈ hierarchy (succ δ), IsInternalForcingTruthTable P R D T :=
  ⟨internalForcingTruthTable P R D, hδ.internalForcingTruthTable_mem_successor hP hD,
    internalForcingTruthTable_correct P R D⟩

end ZFVP
