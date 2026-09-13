import ZFVP.SetTheory.NameEvaluationGraph
import ZFVP.SetTheory.NameRecursionDictionary

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def pairNameFormula : SetTheorySemisentence 4 :=
  f“n p s t. ∀ z, z ∈ n ↔ z = !kpair.dfn s p ∨ z = !kpair.dfn t p”

def orderedPairNameFormula : SetTheorySemisentence 4 :=
  f“n p s t. !pairNameFormula n p (!pairNameFormula p s s) (!pairNameFormula p s t)”

def nameEvaluationGraphFormula : SetTheorySemisentence 3 :=
  f“n p C. ∀ z, z ∈ n ↔ ∃ s ∈ C,
    z = !kpair.dfn (!orderedPairNameFormula p (!checkNameFormula p s) s) p”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance pairNameFormula_defined : ℒₛₑₜ-function₃[V] pairName via pairNameFormula :=
  ⟨fun v ↦ by
    simp [pairNameFormula]
    rw [mem_ext_iff]
    simp [pairName]⟩

instance orderedPairNameFormula_defined :
    ℒₛₑₜ-function₃[V] orderedPairName via orderedPairNameFormula :=
  ⟨fun v ↦ by simp [orderedPairNameFormula, orderedPairName]⟩

instance nameEvaluationGraphFormula_defined :
    ℒₛₑₜ-function₂[V] nameEvaluationGraph via nameEvaluationGraphFormula :=
  ⟨fun v ↦ by
    simp [nameEvaluationGraphFormula]
    rw [mem_ext_iff]
    simp only [mem_nameEvaluationGraph_iff]⟩

instance nameEvaluationGraph_definable : ℒₛₑₜ-function₂[V] nameEvaluationGraph :=
  nameEvaluationGraphFormula_defined.to_definable

end ZFVP
