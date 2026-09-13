import ZFVP.Syntax.Formulas
import ZFVP.Syntax.UniformFormulaCodes
import ZFVP.ModelTheory.FormulaNesting

/-! Shared parameter-free definitions of the internal formula family and its fibers. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def isFormulaClosedFormula : SetTheorySemisentence 3 :=
  f“L Γ Q. ∀ n ∈ !isω,
    (!kpair.dfn n (!truthCodeFormula) ∈ Q ∧ !kpair.dfn n (!falsityCodeFormula) ∈ Q) ∧
    (∀ r args, !isAtomicArgumentsFormula L Γ n r args →
      !kpair.dfn n (!atomCodeFormula r args) ∈ Q ∧ !kpair.dfn n (!negAtomCodeFormula r args) ∈ Q) ∧
    (∀ φ ψ, !kpair.dfn n φ ∈ Q → !kpair.dfn n ψ ∈ Q →
      !kpair.dfn n (!andCodeFormula φ ψ) ∈ Q ∧ !kpair.dfn n (!orCodeFormula φ ψ) ∈ Q) ∧
    ∀ φ, !kpair.dfn (!succ.dfn n) φ ∈ Q →
      !kpair.dfn n (!allCodeFormula φ) ∈ Q ∧ !kpair.dfn n (!existsCodeFormula φ) ∈ Q”

def formulaFamilyFormula : SetTheorySemisentence 3 :=
  f“F L Γ. ∀ p, p ∈ F ↔ p ∈ !syntaxUniverseFormula L Γ ∧
    ∀ Q, !isFormulaClosedFormula L Γ Q → p ∈ Q”

def formulaSetFormula : SetTheorySemisentence 4 :=
  f“F L Γ n. ∀ φ, φ ∈ F ↔ !kpair.dfn n φ ∈ !formulaFamilyFormula L Γ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance isFormulaClosedFormula_defined : ℒₛₑₜ-relation₃[V] IsFormulaClosed via isFormulaClosedFormula :=
  ⟨fun v ↦ by simp [isFormulaClosedFormula, IsFormulaClosed]⟩

instance formulaFamilyFormula_defined : ℒₛₑₜ-function₂[V] formulaFamily via formulaFamilyFormula :=
  ⟨fun v ↦ by
    change formulaFamilyFormula.Evalb v ↔ v 0 = formulaFamily (v 1) (v 2)
    rw [mem_ext_iff]
    simp [formulaFamilyFormula, mem_formulaFamily_iff]⟩

instance formulaSetFormula_defined : ℒₛₑₜ-function₃[V] formulaSet via formulaSetFormula :=
  ⟨fun v ↦ by
    change formulaSetFormula.Evalb v ↔ v 0 = formulaSet (v 1) (v 2) (v 3)
    rw [mem_ext_iff]
    simp [formulaSetFormula, mem_formulaSet_iff]⟩

end ZFVP

