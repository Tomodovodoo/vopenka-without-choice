import ZFVP.SetTheory.UniformNameEvaluation
import ZFVP.SetTheory.ForcingSequenceNames
import ZFVP.ModelTheory.TransitiveZFNames
import ZFVP.ModelTheory.NormalizedPoolRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sequenceNameFormula : SetTheorySemisentence 3 :=
  f“y o s. ∀ z, z ∈ y ↔ ∃ i ∈ !domain.dfn s,
    z = !kpair.dfn (!orderedPairNameFormula o (!checkNameFormula o i) (!value.dfn s i)) o”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance sequenceNameFormula_defined : ℒₛₑₜ-function₂[V] sequenceName via sequenceNameFormula := by
  refine ⟨fun v ↦ ?_⟩
  change sequenceNameFormula.Evalb v ↔ v 0 = sequenceName (v 1) (v 2)
  rw [mem_ext_iff]
  simp [sequenceNameFormula, mem_sequenceName]

namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem pairName_val (o s t : SetDomain U) : (pairName o s t).val = pairName o.val s.val t.val := by
  simp only [pairName, pair_eq_doubleton, doubleton_val, kpair_val]

theorem orderedPairName_val (o s t : SetDomain U) :
    (orderedPairName o s t).val = orderedPairName o.val s.val t.val := by
  simp only [orderedPairName, pairName_val]

theorem sequenceName_val (o s : SetDomain U) : (sequenceName o s).val = sequenceName o.val s.val := by
  unfold sequenceName
  rw [← domain_val U s]
  apply repl_val U
  intro i _
  rw [kpair_val U, orderedPairName_val U, checkName_val U, value_val_total U]

end TransitiveZF

theorem IsChoicelessInaccessible.sequenceName_mem_hierarchy {δ o s : V}
    (hδ : IsChoicelessInaccessible δ) (ho : o ∈ hierarchy δ) (hs : s ∈ hierarchy δ) :
    sequenceName o s ∈ hierarchy δ := by
  let := hδ.1
  let := hierarchy_transitive δ
  let := rankDomain_nonempty hδ.2.1
  let := hδ.rankCriterion.models_zf
  let o' : SetDomain (hierarchy δ) := ⟨o, ho⟩
  let s' : SetDomain (hierarchy δ) := ⟨s, hs⟩
  exact (TransitiveZF.sequenceName_val (hierarchy δ) o' s') ▸ (sequenceName o' s').property

end ZFVP
