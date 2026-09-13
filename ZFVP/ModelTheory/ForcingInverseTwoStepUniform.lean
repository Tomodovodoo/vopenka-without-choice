import ZFVP.ModelTheory.ForcingSuccessorUniform
import ZFVP.ModelTheory.ForcingLimitUniform
import ZFVP.ModelTheory.InverseTwoStepCode
import ZFVP.SetTheory.UniformFunctionOperations

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def twoStepProjectionFormula : SetTheorySemisentence 5 :=
  f“z P R Q t. ∀ a, a ∈ z ↔ ∃ b ∈ !twoStepConditionsFormula P R Q t, a = !kpair.dfn b (!kpair.π₁.dfn b)”

@[irreducible] def twoStepSectionFormula : SetTheorySemisentence 3 :=
  f“z P t. ∀ a, a ∈ z ↔ ∃ p ∈ P, a = !kpair.dfn p (!kpair.dfn p t)”

@[irreducible] def forcingComposeProjectionColumnFormula : SetTheorySemisentence 4 :=
  f“z θ ρ v. ∀ a, a ∈ z ↔ ∃ i ∈ θ, a = !kpair.dfn i (!composeFormula v (!value.dfn ρ i))”

@[irreducible] def forcingComposeSectionColumnFormula : SetTheorySemisentence 4 :=
  f“z θ F e. ∀ a, a ∈ z ↔ ∃ i ∈ θ, a = !kpair.dfn i (!composeFormula (!value.dfn F i) e)”

@[irreducible] def forcingTwoStepLiftColumnFormula : SetTheorySemisentence 5 :=
  f“z θ D P M. ∀ a, a ∈ z ↔ ∃ i ∈ θ, a = !kpair.dfn i (!successorForcingLiftFormula D (!value.dfn P i) (!value.dfn M i))”

@[irreducible] def forcingInverseTwoStepCodeFormula : SetTheorySemisentence 6 :=
  f“z θ s Q S u. ∀ C, !forcingInverseLimitFormula C θ (!forcingCodePFormula s)
    (!forcingCodeπFormula s) (!forcingCodeUniverseFormula s) →
    ∀ U, !forcingThreadOrderFormula U θ (!forcingCodeRFormula s) C →
    !forcingIterationCodeNextFormula z θ s (!twoStepConditionsFormula C U Q u) (!twoStepOrderFormula C U Q S u)
      (!forcingComposeProjectionColumnFormula θ (!forcingLimitProjectionColumnFormula θ C) (!twoStepProjectionFormula C U Q u))
      (!forcingComposeSectionColumnFormula θ
        (!forcingLimitSectionColumnFormula θ (!forcingCodePFormula s) (!forcingCodeπFormula s) (!forcingCodeEFormula s))
        (!twoStepSectionFormula C u))
      (!forcingTwoStepLiftColumnFormula θ (!twoStepConditionsFormula C U Q u) (!forcingCodePFormula s)
        (!forcingLimitLiftColumnFormula C θ (!forcingCodePFormula s) (!forcingCodeπFormula s) (!forcingCodeLFormula s)))
      (!kpair.dfn (!forcingSectionThreadFormula θ (!forcingCodeπFormula s) (!forcingCodeEFormula s)
        (!isEmpty) (!value.dfn (!forcingCodetFormula s) (!isEmpty))) u)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance twoStepProjectionFormula_defined : ℒₛₑₜ-function₄[V] twoStepProjection via twoStepProjectionFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [twoStepProjectionFormula, twoStepProjection, mem_definableGraph_iff]⟩

instance twoStepSectionFormula_defined : ℒₛₑₜ-function₂[V] twoStepSection via twoStepSectionFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [twoStepSectionFormula, twoStepSection, mem_definableGraph_iff]⟩

instance forcingComposeProjectionColumnFormula_defined : ℒₛₑₜ-function₃[V] forcingComposeProjectionColumn via forcingComposeProjectionColumnFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [forcingComposeProjectionColumnFormula, forcingComposeProjectionColumn, mem_definableGraph_iff]⟩

instance forcingComposeSectionColumnFormula_defined : ℒₛₑₜ-function₃[V] forcingComposeSectionColumn via forcingComposeSectionColumnFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [forcingComposeSectionColumnFormula, forcingComposeSectionColumn, mem_definableGraph_iff]⟩

instance forcingTwoStepLiftColumnFormula_defined : ℒₛₑₜ-function₄[V] forcingTwoStepLiftColumn via forcingTwoStepLiftColumnFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [forcingTwoStepLiftColumnFormula, forcingTwoStepLiftColumn, mem_definableGraph_iff]⟩

instance forcingInverseTwoStepCodeFormula_defined :
    ℒₛₑₜ-function₅[V] forcingInverseTwoStepCode via forcingInverseTwoStepCodeFormula :=
  ⟨fun v ↦ by simp [forcingInverseTwoStepCodeFormula, forcingInverseTwoStepCode, forcingTwoStepColumnCode]⟩

end ZFVP
