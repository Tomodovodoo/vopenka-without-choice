import ZFVP.ModelTheory.SchmerlInternalInfinitaryInduction
import ZFVP.Syntax.UniformSatisfaction

/-! Fixed formulas for internal infinitary fragments and their dependency
relations. The dictionary has no ambient-model parameter. -/

namespace ZFVP.Infinitary.Internal

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def foCodeFormula : SetTheorySemisentence 2 := f“z φ. z = !kpair.dfn (!(numeralFormula 0)) φ”
def negCodeFormula : SetTheorySemisentence 2 := f“z φ. z = !kpair.dfn (!(numeralFormula 1)) φ”
def conjCodeFormula : SetTheorySemisentence 2 := f“z φ. z = !kpair.dfn (!(numeralFormula 2)) φ”
def exsCodeFormula : SetTheorySemisentence 2 := f“z φ. z = !kpair.dfn (!(numeralFormula 3)) φ”
def qCodeFormula : SetTheorySemisentence 2 := f“z φ. z = !kpair.dfn (!(numeralFormula 4)) φ”

def isNodeFormula : SetTheorySemisentence 4 :=
  f“L F n φ. n ∈ !isω ∧
    ((∃ ψ ∈ !formulaSetFormula L (!isEmpty) n, φ = !foCodeFormula ψ) ∨
      (∃ ψ, φ = !negCodeFormula ψ ∧ !kpair.dfn n ψ ∈ F) ∨
      (∃ f, !IsFunction.dfn f ∧ !domain.dfn f = !isω ∧ φ = !conjCodeFormula f ∧
        ∀ i ∈ !isω, !kpair.dfn n (!value.dfn f i) ∈ F) ∨
      (∃ ψ, φ = !exsCodeFormula ψ ∧ !kpair.dfn (!succ.dfn n) ψ ∈ F) ∨
      ∃ ψ, φ = !qCodeFormula ψ ∧ !kpair.dfn (!succ.dfn n) ψ ∈ F)”

def isFragmentFormula : SetTheorySemisentence 2 :=
  f“L F. !isLanguageCodeFormula L ∧ ∀ t ∈ F,
    t = !kpair.dfn (!kpair.π₁.dfn t) (!kpair.π₂.dfn t) ∧
    !isNodeFormula L F (!kpair.π₁.dfn t) (!kpair.π₂.dfn t)”

def isImmediateFormula : SetTheorySemisentence 2 :=
  f“s t. (∃ n φ, t = !kpair.dfn n (!negCodeFormula φ) ∧ s = !kpair.dfn n φ) ∨
    (∃ n f i, !IsFunction.dfn f ∧ i ∈ !domain.dfn f ∧
      t = !kpair.dfn n (!conjCodeFormula f) ∧ s = !kpair.dfn n (!value.dfn f i)) ∨
    ∃ n φ, (t = !kpair.dfn n (!exsCodeFormula φ) ∨ t = !kpair.dfn n (!qCodeFormula φ)) ∧
      s = !kpair.dfn (!succ.dfn n) φ”

def immediateRelationFormula : SetTheorySemisentence 2 :=
  f“R F. ∀ p, p ∈ R ↔ p ∈ !prod.dfn F F ∧ !isImmediateFormula (!kpair.π₁.dfn p) (!kpair.π₂.dfn p)”

def depthDomainFormula : SetTheorySemisentence 2 := f“D F. D = !prod.dfn F (!isω)”

def depthRelationFormula : SetTheorySemisentence 2 :=
  f“R D. ∀ p, p ∈ R ↔ p ∈ !prod.dfn D D ∧
    !isImmediateFormula (!kpair.π₁.dfn (!kpair.π₁.dfn p)) (!kpair.π₁.dfn (!kpair.π₂.dfn p))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance foCodeFormula_defined : ℒₛₑₜ-function₁[V] foCode via foCodeFormula :=
  ⟨fun v ↦ by simp [foCodeFormula, foCode]⟩
instance negCodeFormula_defined : ℒₛₑₜ-function₁[V] negCode via negCodeFormula :=
  ⟨fun v ↦ by simp [negCodeFormula, negCode]⟩
instance conjCodeFormula_defined : ℒₛₑₜ-function₁[V] conjCode via conjCodeFormula :=
  ⟨fun v ↦ by simp [conjCodeFormula, conjCode]⟩
instance exsCodeFormula_defined : ℒₛₑₜ-function₁[V] exsCode via exsCodeFormula :=
  ⟨fun v ↦ by simp [exsCodeFormula, exsCode]⟩
instance qCodeFormula_defined : ℒₛₑₜ-function₁[V] qCode via qCodeFormula :=
  ⟨fun v ↦ by simp [qCodeFormula, qCode]⟩

instance isNodeFormula_defined : ℒₛₑₜ-relation₄[V] IsNode via isNodeFormula :=
  ⟨fun v ↦ by simp [isNodeFormula, IsNode]⟩
instance isFragmentFormula_defined : ℒₛₑₜ-relation[V] IsFragment via isFragmentFormula :=
  ⟨fun v ↦ by simp [isFragmentFormula, IsFragment]⟩
instance isImmediateFormula_defined : ℒₛₑₜ-relation[V] IsImmediate via isImmediateFormula :=
  ⟨fun v ↦ by simp [isImmediateFormula, IsImmediate]⟩

instance immediateRelationFormula_defined : ℒₛₑₜ-function₁[V] immediateRelation via immediateRelationFormula :=
  ⟨fun v ↦ by
    change immediateRelationFormula.Evalb v ↔ v 0 = immediateRelation (v 1)
    rw [mem_ext_iff]
    simp [immediateRelationFormula, immediateRelation]⟩

instance depthDomainFormula_defined : ℒₛₑₜ-function₁[V] depthDomain via depthDomainFormula :=
  ⟨fun v ↦ by simp [depthDomainFormula, depthDomain]⟩

instance depthRelationFormula_defined : ℒₛₑₜ-function₁[V] depthRelation via depthRelationFormula :=
  ⟨fun v ↦ by
    change depthRelationFormula.Evalb v ↔ v 0 = depthRelation (v 1)
    rw [mem_ext_iff]
    simp [depthRelationFormula, depthRelation]⟩

end ZFVP.Infinitary.Internal
