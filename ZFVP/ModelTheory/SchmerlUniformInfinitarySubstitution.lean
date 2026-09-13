import ZFVP.ModelTheory.SchmerlUniformInfinitaryTruth
import ZFVP.ModelTheory.SchmerlInternalInfinitarySubstitutionSemantics
import ZFVP.Syntax.UniformFormulaSubstitution

/-! Fixed definitions for actual infinitary substitution and its image
fragment. These definitions support elementary transfer of proof syntax. -/

namespace ZFVP.Infinitary.Internal

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def transformConjunctionFormula : SetTheorySemisentence 4 :=
  f“g q previous f. ∀ p, p ∈ g ↔ ∃ i ∈ !isω,
    p = !kpair.dfn i (!value.dfn previous (!substitutionChildFormula q (!value.dfn f i)))”

def infinitarySubstitutionStepFormula : SetTheorySemisentence 5 :=
  f“z L G q previous. ∀ φ, φ = !kpair.π₂.dfn (!kpair.π₁.dfn q) →
    ∀ t, t = !kpair.π₁.dfn φ → ∀ d, d = !kpair.π₂.dfn φ →
    (t = !(numeralFormula 0) ∧ z = !foCodeFormula
      (!value.dfn (!formulaSubstitutionGraphFormula L (!isEmpty) G)
        (!kpair.dfn (!kpair.dfn (!kpair.π₁.dfn (!kpair.π₁.dfn q)) d) (!kpair.π₂.dfn q)))) ∨
    (t ≠ !(numeralFormula 0) ∧ t = !(numeralFormula 1) ∧
      z = !negCodeFormula (!value.dfn previous (!substitutionChildFormula q d))) ∨
    (t ≠ !(numeralFormula 0) ∧ t ≠ !(numeralFormula 1) ∧ t = !(numeralFormula 2) ∧
      z = !conjCodeFormula (!transformConjunctionFormula q previous d)) ∨
    (t ≠ !(numeralFormula 0) ∧ t ≠ !(numeralFormula 1) ∧ t ≠ !(numeralFormula 2) ∧ t = !(numeralFormula 3) ∧
      z = !exsCodeFormula (!value.dfn previous (!substitutionBodyFormula q d))) ∨
    (t ≠ !(numeralFormula 0) ∧ t ≠ !(numeralFormula 1) ∧ t ≠ !(numeralFormula 2) ∧ t ≠ !(numeralFormula 3) ∧
      z = !qCodeFormula (!value.dfn previous (!substitutionBodyFormula q d)))”

def infinitarySubstitutionGraphFormula : SetTheorySemisentence 4 :=
  f“g L F G. !IsFunction.dfn g ∧ !domain.dfn g = !depthDomainFormula F ∧
    ∀ q ∈ !depthDomainFormula F, !value.dfn g q = !infinitarySubstitutionStepFormula L G q
      (!restrict.dfn g (!predecessorsFormula (!depthRelationFormula (!depthDomainFormula F)) (!depthDomainFormula F) q))”

def substitutionDepthsFormula : SetTheorySemisentence 3 :=
  f“S F G. ∀ q, q ∈ S ↔ q ∈ !depthDomainFormula F ∧
    !kpair.π₁.dfn (!kpair.π₁.dfn q) = !stateSourceFormula (!value.dfn G (!kpair.π₂.dfn q))”

def substitutedNodeFormula : SetTheorySemisentence 5 :=
  f“p L F G q. p = !kpair.dfn (!stateTargetFormula (!value.dfn G (!kpair.π₂.dfn q)))
    (!value.dfn (!infinitarySubstitutionGraphFormula L F G) q)”

def substitutedFragmentFormula : SetTheorySemisentence 4 :=
  f“S L F G. ∀ p, p ∈ S ↔ ∃ q ∈ !substitutionDepthsFormula F G, p = !substitutedNodeFormula L F G q”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance transformConjunctionFormula_defined :
    ℒₛₑₜ-function₃[V] transformConjunction via transformConjunctionFormula :=
  ⟨fun v ↦ by
    change transformConjunctionFormula.Evalb v ↔ v 0 = transformConjunction (v 1) (v 2) (v 3)
    rw [mem_ext_iff]
    simp [transformConjunctionFormula, transformConjunction, mem_definableGraph_iff]⟩

instance infinitarySubstitutionStepFormula_defined :
    ℒₛₑₜ-function₄[V] infinitarySubstitutionStep via infinitarySubstitutionStepFormula :=
  ⟨fun v ↦ by
    simp only [infinitarySubstitutionStepFormula]
    simp
    unfold infinitarySubstitutionStep
    dsimp
    split <;> simp_all
    split <;> simp_all
    split <;> simp_all
    split <;> simp_all⟩

instance infinitarySubstitutionGraphFormula_defined :
    ℒₛₑₜ-function₃[V] infinitarySubstitutionGraph via infinitarySubstitutionGraphFormula :=
  ⟨fun v ↦ by
    change infinitarySubstitutionGraphFormula.Evalb v ↔ v 0 = infinitarySubstitutionGraph (v 1) (v 2) (v 3)
    rw [eq_comm]
    unfold infinitarySubstitutionGraph depthRecursion
    rw [wellFoundedRecursion_eq_iff, totalRecursionAttempt_iff]
    simp [infinitarySubstitutionGraphFormula]⟩

instance substitutionDepthsFormula_defined :
    ℒₛₑₜ-function₂[V] substitutionDepths via substitutionDepthsFormula :=
  ⟨fun v ↦ by
    change substitutionDepthsFormula.Evalb v ↔ v 0 = substitutionDepths (v 1) (v 2)
    rw [mem_ext_iff]
    simp [substitutionDepthsFormula, substitutionDepths]⟩

instance substitutedNodeFormula_defined : ℒₛₑₜ-function₄[V] substitutedNode via substitutedNodeFormula :=
  ⟨fun v ↦ by simp [substitutedNodeFormula, substitutedNode]⟩

instance substitutedFragmentFormula_defined : ℒₛₑₜ-function₃[V] substitutedFragment via substitutedFragmentFormula :=
  ⟨fun v ↦ by
    change substitutedFragmentFormula.Evalb v ↔ v 0 = substitutedFragment (v 1) (v 2) (v 3)
    rw [mem_ext_iff]
    simp [substitutedFragmentFormula, substitutedFragment, repl_spec]⟩

end ZFVP.Infinitary.Internal
