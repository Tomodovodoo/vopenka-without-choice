import ZFVP.ModelTheory.ForcingCodeConstructionUniform
import ZFVP.SetTheory.ForcingLimitColumnDefinability

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def forcingSectionValueFormula : SetTheorySemisentence 6 :=
  f“z π E k p i. (i ∈ k ∧ !value.dfn z (!value.dfn π (!kpair.dfn i k)) p) ∨ (i ∉ k ∧ !value.dfn z (!value.dfn E (!kpair.dfn k i)) p)”

@[irreducible] def forcingSectionThreadFormula : SetTheorySemisentence 6 :=
  f“z θ π E k p. ∀ a, a ∈ z ↔ ∃ i ∈ θ, a = !kpair.dfn i (!forcingSectionValueFormula π E k p i)”

@[irreducible] def forcingThreadSectionFormula : SetTheorySemisentence 6 :=
  f“z θ P π E i. ∀ a, a ∈ z ↔ ∃ p ∈ !value.dfn P i, a = !kpair.dfn p (!forcingSectionThreadFormula θ π E i p)”

@[irreducible] def forcingLimitProjectionColumnFormula : SetTheorySemisentence 3 :=
  f“z θ C. ∀ a, a ∈ z ↔ ∃ i ∈ θ, a = !kpair.dfn i (!forcingThreadCoordinateFormula C i)”

@[irreducible] def forcingLimitSectionColumnFormula : SetTheorySemisentence 5 :=
  f“z θ P π E. ∀ a, a ∈ z ↔ ∃ i ∈ θ, a = !kpair.dfn i (!forcingThreadSectionFormula θ P π E i)”

@[irreducible] def forcingThreadSplicePairFormula : SetTheorySemisentence 6 :=
  f“z θ π L i a. ∀ b, b ∈ z ↔ ∃ j ∈ θ, (j ∈ i ∧ b = !kpair.dfn j (!value.dfn (!value.dfn π (!kpair.dfn j i)) (!kpair.π₂.dfn a))) ∨ (j ∉ i ∧ b = !kpair.dfn j (!value.dfn (!value.dfn L (!kpair.dfn i j)) (!kpair.dfn (!value.dfn (!kpair.π₁.dfn a) j) (!kpair.π₂.dfn a))))”

@[irreducible] def forcingLimitLiftFormula : SetTheorySemisentence 7 :=
  f“z C A θ π L i. ∀ b, b ∈ z ↔ ∃ a ∈ !prod.dfn C A, b = !kpair.dfn a (!forcingThreadSplicePairFormula θ π L i a)”

@[irreducible] def forcingLimitLiftColumnFormula : SetTheorySemisentence 6 :=
  f“z C θ P π L. ∀ a, a ∈ z ↔ ∃ i ∈ θ, a = !kpair.dfn i (!forcingLimitLiftFormula C (!value.dfn P i) θ π L i)”

@[irreducible] def forcingThreadCodeFormula : SetTheorySemisentence 4 :=
  f“z θ s C. !forcingIterationCodeNextFormula z θ s C
    (!forcingThreadOrderFormula θ (!forcingCodeRFormula s) C)
    (!forcingLimitProjectionColumnFormula θ C)
    (!forcingLimitSectionColumnFormula θ (!forcingCodePFormula s) (!forcingCodeπFormula s) (!forcingCodeEFormula s))
    (!forcingLimitLiftColumnFormula C θ (!forcingCodePFormula s) (!forcingCodeπFormula s) (!forcingCodeLFormula s))
    (!forcingSectionThreadFormula θ (!forcingCodeπFormula s) (!forcingCodeEFormula s) (!isEmpty)
      (!value.dfn (!forcingCodetFormula s) (!isEmpty)))”

@[irreducible] def forcingDirectCodeFormula : SetTheorySemisentence 3 :=
  f“z θ s. !forcingThreadCodeFormula z θ s (!forcingDirectLimitFormula θ (!forcingCodePFormula s)
    (!forcingCodeπFormula s) (!forcingCodeEFormula s) (!forcingCodeUniverseFormula s))”

@[irreducible] def forcingInverseCodeFormula : SetTheorySemisentence 3 :=
  f“z θ s. !forcingThreadCodeFormula z θ s (!forcingInverseLimitFormula θ (!forcingCodePFormula s)
    (!forcingCodeπFormula s) (!forcingCodeUniverseFormula s))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingSectionValueFormula_defined : ℒₛₑₜ-function₅[V] forcingSectionValue via forcingSectionValueFormula :=
  ⟨fun v ↦ by classical
    by_cases h : v 5 ∈ v 3 <;> simp [forcingSectionValueFormula, forcingSectionValue, h]⟩

instance forcingSectionThreadFormula_defined : ℒₛₑₜ-function₅[V] forcingSectionThread via forcingSectionThreadFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [forcingSectionThreadFormula, forcingSectionThread, mem_definableGraph_iff]⟩

instance forcingThreadSectionFormula_defined : ℒₛₑₜ-function₅[V] forcingThreadSection via forcingThreadSectionFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [forcingThreadSectionFormula, forcingThreadSection, mem_definableGraph_iff]⟩

instance forcingLimitProjectionColumnFormula_defined : ℒₛₑₜ-function₂[V] forcingLimitProjectionColumn via forcingLimitProjectionColumnFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [forcingLimitProjectionColumnFormula, forcingLimitProjectionColumn, mem_definableGraph_iff]⟩

instance forcingLimitSectionColumnFormula_defined : ℒₛₑₜ-function₄[V] forcingLimitSectionColumn via forcingLimitSectionColumnFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [forcingLimitSectionColumnFormula, forcingLimitSectionColumn, mem_definableGraph_iff]⟩

instance forcingThreadSplicePairFormula_defined : ℒₛₑₜ-function₅[V] forcingThreadSplicePair via forcingThreadSplicePairFormula :=
  ⟨fun v ↦ by classical
    rw [mem_ext_iff]
    simp only [forcingThreadSplicePairFormula]
    simp
    apply forall_congr'
    intro z
    rw [forcingThreadSplicePair, forcingThreadSplice, mem_definableGraph_iff]
    apply iff_congr Iff.rfl
    apply exists_congr
    intro j
    by_cases hj : j ∈ v 4 <;> simp [forcingSpliceValue, hj]⟩

instance forcingLimitLiftFormula_defined : Defined (fun v : Fin 7 → V ↦ v 0 = forcingLimitLift (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) forcingLimitLiftFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [forcingLimitLiftFormula, forcingLimitLift, mem_definableGraph_iff, forcingThreadSplicePair]⟩

instance forcingLimitLiftColumnFormula_defined : ℒₛₑₜ-function₅[V] forcingLimitLiftColumn via forcingLimitLiftColumnFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [forcingLimitLiftColumnFormula, forcingLimitLiftColumn, mem_definableGraph_iff]⟩

instance forcingThreadCodeFormula_defined : ℒₛₑₜ-function₃[V] forcingThreadCode via forcingThreadCodeFormula :=
  ⟨fun v ↦ by simp [forcingThreadCodeFormula, forcingThreadCode]⟩

instance forcingDirectCodeFormula_defined : ℒₛₑₜ-function₂[V] forcingDirectCode via forcingDirectCodeFormula :=
  ⟨fun v ↦ by simp [forcingDirectCodeFormula, forcingDirectCode]⟩

instance forcingInverseCodeFormula_defined : ℒₛₑₜ-function₂[V] forcingInverseCode via forcingInverseCodeFormula :=
  ⟨fun v ↦ by simp [forcingInverseCodeFormula, forcingInverseCode]⟩

end ZFVP
