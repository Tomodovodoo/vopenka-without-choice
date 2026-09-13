import ZFVP.SetTheory.UniformCollapse
import ZFVP.SetTheory.UniformFunctionOperations

/-! Fixed parameter-free formulas for well-foundedness, extensionality and collapse. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def internallyWellFoundedFormula : SetTheorySemisentence 2 :=
  f“R D. ∀ A, A ⊆ D → !isNonempty A → ∃ x ∈ A, ∀ y ∈ A, !kpair.dfn y x ∉ R”

def extensionalOnFormula : SetTheorySemisentence 2 :=
  f“R D. ∀ x ∈ D, ∀ y ∈ D, (∀ z ∈ D, !kpair.dfn z x ∈ R ↔ !kpair.dfn z y ∈ R) → x = y”

def collapseRecursionFormula : SetTheorySemisentence 3 :=
  f“f R D. !IsFunction.dfn f ∧ !domain.dfn f = D ∧ ∀ x ∈ D,
    !value.dfn f x = !range.dfn (!restrict.dfn f (!predecessorsFormula R D x))”

def mostowskiMapFormula : SetTheorySemisentence 3 :=
  f“f R D. (!internallyWellFoundedFormula R D ∧ !collapseRecursionFormula f R D) ∨
    (¬!internallyWellFoundedFormula R D ∧ !isEmpty f)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance internallyWellFoundedFormula_defined :
    ℒₛₑₜ-relation[V] IsInternallyWellFounded via internallyWellFoundedFormula :=
  ⟨fun v ↦ by simp [internallyWellFoundedFormula, IsInternallyWellFounded, isNonempty_def]⟩

instance extensionalOnFormula_defined : ℒₛₑₜ-relation[V] IsExtensionalOn via extensionalOnFormula :=
  ⟨fun v ↦ by simp [extensionalOnFormula, IsExtensionalOn]⟩

instance collapseRecursionFormula_defined : ℒₛₑₜ-relation₃[V]
    (fun f R D ↦ IsRecursionAttempt R D (fun _ g ↦ range g) f ∧ domain f = D) via collapseRecursionFormula :=
  ⟨fun v ↦ by simp [collapseRecursionFormula, totalRecursionAttempt_iff]⟩

instance mostowskiMapFormula_defined : ℒₛₑₜ-function₂[V] mostowskiMap via mostowskiMapFormula :=
  ⟨fun v ↦ by
    change mostowskiMapFormula.Evalb v ↔ v 0 = mostowskiMap (v 1) (v 2)
    rw [eq_comm, mostowskiMap_eq_iff]
    simp [mostowskiMapFormula, isEmpty_iff_eq_empty]⟩

end ZFVP
