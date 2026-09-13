import ZFVP.Syntax.Subformulas
import ZFVP.Syntax.UniformFormulas

/-! Shared definitions of the context-sensitive subformula relation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def immediateSubformulaFormula : SetTheorySemisentence 2 :=
  f“s t. (∃ n φ ψ, (t = !kpair.dfn n (!andCodeFormula φ ψ) ∨
      t = !kpair.dfn n (!orCodeFormula φ ψ)) ∧ (s = !kpair.dfn n φ ∨ s = !kpair.dfn n ψ)) ∨
    ∃ n φ, (t = !kpair.dfn n (!allCodeFormula φ) ∨ t = !kpair.dfn n (!existsCodeFormula φ)) ∧
      s = !kpair.dfn (!succ.dfn n) φ”

def subformulaRelationFormula : SetTheorySemisentence 2 :=
  f“R F. ∀ p, p ∈ R ↔ p ∈ !prod.dfn F F ∧
    !immediateSubformulaFormula (!kpair.π₁.dfn p) (!kpair.π₂.dfn p)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance immediateSubformulaFormula_defined : ℒₛₑₜ-relation[V] IsImmediateSubformula via immediateSubformulaFormula :=
  ⟨fun v ↦ by simp [immediateSubformulaFormula, IsImmediateSubformula]⟩

instance subformulaRelationFormula_defined : ℒₛₑₜ-function₁[V] subformulaRelation via subformulaRelationFormula :=
  ⟨fun v ↦ by
    change subformulaRelationFormula.Evalb v ↔ v 0 = subformulaRelation (v 1)
    rw [mem_ext_iff]
    simp [subformulaRelationFormula, subformulaRelation]⟩

end ZFVP
