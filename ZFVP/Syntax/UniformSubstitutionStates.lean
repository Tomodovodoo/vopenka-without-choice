import ZFVP.Syntax.SubstitutionStateDefinability
import ZFVP.Syntax.UniformBindingSubstitution
import ZFVP.SetTheory.UniformParameterizedRecursion

/-! Parameter-free definitions for all internal binder-depth substitution states. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def packedSubstitutionStateStepFormula : SetTheorySemisentence 3 :=
  f“z P g. (!domain.dfn g = !(numeralFormula 0) ∧ z = !kpair.π₂.dfn P) ∨
    (!domain.dfn g ≠ !(numeralFormula 0) ∧ z = !liftSubstitutionStateFormula
      (!kpair.π₁.dfn (!kpair.π₁.dfn P)) (!kpair.π₂.dfn (!kpair.π₁.dfn P))
      (!value.dfn g (!sUnion.dfn (!domain.dfn g))))”

def packedSubstitutionStateAtFormula : SetTheorySemisentence 3 :=
  parameterRecursionFormula packedSubstitutionStateStepFormula

def substitutionStateAtFormula : SetTheorySemisentence 5 :=
  f“y L Δ s k. y = !packedSubstitutionStateAtFormula (!kpair.dfn (!kpair.dfn L Δ) s) k”

def substitutionStatesFormula : SetTheorySemisentence 4 :=
  f“G L Δ s. ∀ p, p ∈ G ↔ ∃ k ∈ !isω, p = !kpair.dfn k (!substitutionStateAtFormula L Δ s k)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance packedSubstitutionStateStepFormula_defined :
    ℒₛₑₜ-function₂[V] packedSubstitutionStateStep via packedSubstitutionStateStepFormula :=
  ⟨fun v ↦ by
    by_cases h : domain (v 2) = 0 <;>
      simp [packedSubstitutionStateStepFormula, packedSubstitutionStateStep, naturalIterationStep, h]⟩

instance packedSubstitutionStateAtFormula_defined :
    ℒₛₑₜ-function₂[V] packedSubstitutionStateAt via packedSubstitutionStateAtFormula :=
  parameterRecursionFormula_defined packedSubstitutionStateStep packedSubstitutionStateStepFormula

instance substitutionStateAtFormula_defined :
    ℒₛₑₜ-function₄[V] substitutionStateAt via substitutionStateAtFormula :=
  ⟨fun v ↦ by simp [substitutionStateAtFormula, substitutionStateAt]⟩

instance substitutionStatesFormula_defined : ℒₛₑₜ-function₃[V] substitutionStates via substitutionStatesFormula :=
  ⟨fun v ↦ by
    change substitutionStatesFormula.Evalb v ↔ v 0 = substitutionStates (v 1) (v 2) (v 3)
    rw [mem_ext_iff]
    simp [substitutionStatesFormula, substitutionStates, naturalIterationGraph,
      mem_definableGraph_iff, substitutionStateAt_eq]⟩

end ZFVP
