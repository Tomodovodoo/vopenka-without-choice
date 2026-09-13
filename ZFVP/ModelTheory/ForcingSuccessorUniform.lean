import ZFVP.ModelTheory.ForcingCodeConstructionUniform

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def successorStageProjectionFormula : SetTheorySemisentence 5 :=
  f“z C π k i. ∀ a, a ∈ z ↔ ∃ b ∈ C, a = !kpair.dfn b (!value.dfn (!value.dfn π (!kpair.dfn i k)) (!kpair.π₁.dfn b))”

@[irreducible] def successorStageSectionFormula : SetTheorySemisentence 6 :=
  f“z P E k t i. ∀ a, a ∈ z ↔ ∃ p ∈ !value.dfn P i, a = !kpair.dfn p (!kpair.dfn (!value.dfn (!value.dfn E (!kpair.dfn i k)) p) t)”

@[irreducible] def successorForcingLiftValueFormula : SetTheorySemisentence 4 :=
  f“z L a b. z = !kpair.dfn (!value.dfn L (!kpair.dfn (!kpair.π₁.dfn a) b)) (!kpair.π₂.dfn a)”

@[irreducible] def successorForcingLiftFormula : SetTheorySemisentence 4 :=
  f“z C A L. ∀ a, a ∈ z ↔ ∃ b ∈ !prod.dfn C A, a = !kpair.dfn b (!successorForcingLiftValueFormula L (!kpair.π₁.dfn b) (!kpair.π₂.dfn b))”

@[irreducible] def successorProjectionColumnFormula : SetTheorySemisentence 5 :=
  f“z θ C π k. ∀ a, a ∈ z ↔ ∃ i ∈ θ, a = !kpair.dfn i (!successorStageProjectionFormula C π k i)”

@[irreducible] def successorSectionColumnFormula : SetTheorySemisentence 6 :=
  f“z θ P E k t. ∀ a, a ∈ z ↔ ∃ i ∈ θ, a = !kpair.dfn i (!successorStageSectionFormula P E k t i)”

@[irreducible] def successorLiftColumnFormula : SetTheorySemisentence 6 :=
  f“z θ C P L k. ∀ a, a ∈ z ↔ ∃ i ∈ θ, a = !kpair.dfn i (!successorForcingLiftFormula C (!value.dfn P i) (!value.dfn L (!kpair.dfn i k)))”

@[irreducible] def forcingSuccessorCodeFormula : SetTheorySemisentence 6 :=
  f“z k s Q S u. ∀ C, !twoStepConditionsFormula C (!value.dfn (!forcingCodePFormula s) k)
    (!value.dfn (!forcingCodeRFormula s) k) Q u →
    !forcingIterationCodeNextFormula z (!succ.dfn k) s C
      (!twoStepOrderFormula (!value.dfn (!forcingCodePFormula s) k) (!value.dfn (!forcingCodeRFormula s) k) Q S u)
      (!successorProjectionColumnFormula (!succ.dfn k) C (!forcingCodeπFormula s) k)
      (!successorSectionColumnFormula (!succ.dfn k) (!forcingCodePFormula s) (!forcingCodeEFormula s) k u)
      (!successorLiftColumnFormula (!succ.dfn k) C (!forcingCodePFormula s) (!forcingCodeLFormula s) k)
      (!kpair.dfn (!value.dfn (!forcingCodetFormula s) k) u)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance successorStageProjectionFormula_defined : ℒₛₑₜ-function₄[V] successorStageProjection via successorStageProjectionFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [successorStageProjectionFormula, successorStageProjection, mem_definableGraph_iff]⟩

instance successorStageSectionFormula_defined : ℒₛₑₜ-function₅[V] successorStageSection via successorStageSectionFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [successorStageSectionFormula, successorStageSection, mem_definableGraph_iff]⟩

instance successorForcingLiftValueFormula_defined : ℒₛₑₜ-function₃[V] successorForcingLiftValue via successorForcingLiftValueFormula :=
  ⟨fun v ↦ by simp [successorForcingLiftValueFormula, successorForcingLiftValue, twoStepStronger]⟩

instance successorForcingLiftFormula_defined : ℒₛₑₜ-function₃[V] successorForcingLift via successorForcingLiftFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [successorForcingLiftFormula, successorForcingLift, mem_definableGraph_iff]⟩

instance successorProjectionColumnFormula_defined : ℒₛₑₜ-function₄[V] successorProjectionColumn via successorProjectionColumnFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [successorProjectionColumnFormula, successorProjectionColumn, mem_definableGraph_iff]⟩

instance successorSectionColumnFormula_defined : ℒₛₑₜ-function₅[V] successorSectionColumn via successorSectionColumnFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [successorSectionColumnFormula, successorSectionColumn, mem_definableGraph_iff]⟩

instance successorLiftColumnFormula_defined : ℒₛₑₜ-function₅[V] successorLiftColumn via successorLiftColumnFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [successorLiftColumnFormula, successorLiftColumn, mem_definableGraph_iff]⟩

instance forcingSuccessorCodeFormula_defined :
    ℒₛₑₜ-function₅[V] forcingSuccessorCode via forcingSuccessorCodeFormula :=
  ⟨fun v ↦ by simp [forcingSuccessorCodeFormula, forcingSuccessorCode]⟩

end ZFVP
