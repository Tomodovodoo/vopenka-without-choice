import ZFVP.SetTheory.NameRecursionDictionary
import ZFVP.SetTheory.SymmetricSystems

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def nameStabilizerFormula : SetTheorySemisentence 3 :=
  f“H G t. ∀ p, p ∈ H ↔ p ∈ G ∧ !nameActionFormula p t = t”

def symmetricNameFormula : SetTheorySemisentence 4 :=
  f“P G F t. !forcingNameFormula P t ∧ !nameStabilizerFormula G t ∈ F”

def hereditarilySymmetricNameFormula : SetTheorySemisentence 4 :=
  f“P G F t. !forcingNameFormula P t ∧ ∀ s ∈ !nameClosureFormula t, !nameStabilizerFormula G s ∈ F”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance nameStabilizerFormula_defined : ℒₛₑₜ-function₂[V] nameStabilizer via nameStabilizerFormula :=
  ⟨fun v ↦ by
    change nameStabilizerFormula.Evalb v ↔ v 0 = nameStabilizer (v 1) (v 2)
    rw [mem_ext_iff]
    simp [nameStabilizerFormula, nameStabilizer]⟩

instance symmetricNameFormula_defined : ℒₛₑₜ-relation₄[V] IsSymmetricName via symmetricNameFormula :=
  ⟨fun v ↦ by simp [symmetricNameFormula, IsSymmetricName]⟩

instance hereditarilySymmetricNameFormula_defined :
    ℒₛₑₜ-relation₄[V] IsHereditarilySymmetricName via hereditarilySymmetricNameFormula :=
  ⟨fun v ↦ by simp [hereditarilySymmetricNameFormula, IsHereditarilySymmetricName]⟩

end ZFVP
