import ZFVP.Syntax.FormulaNesting
import ZFVP.ModelTheory.ForcingSuccessorDefinability
import ZFVP.ModelTheory.ForcingLimitFormulas

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def forcingCodePFormula : SetTheorySemisentence 2 :=
  f“z s. z = !kpair.π₁.dfn s”

@[irreducible] def forcingCodeRFormula : SetTheorySemisentence 2 :=
  f“z s. z = !kpair.π₁.dfn (!kpair.π₂.dfn s)”

@[irreducible] def forcingCodeπFormula : SetTheorySemisentence 2 :=
  f“z s. z = !kpair.π₁.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn s))”

@[irreducible] def forcingCodeEFormula : SetTheorySemisentence 2 :=
  f“z s. z = !kpair.π₁.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn s)))”

@[irreducible] def forcingCodeLFormula : SetTheorySemisentence 2 :=
  f“z s. z = !kpair.π₁.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn s))))”

@[irreducible] def forcingCodetFormula : SetTheorySemisentence 2 :=
  f“z s. z = !kpair.π₂.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn s))))”

@[irreducible] def forcingIterationCodeFormula : SetTheorySemisentence 7 :=
  f“z P R π E L t. z = !kpair.dfn P (!kpair.dfn R (!kpair.dfn π (!kpair.dfn E (!kpair.dfn L t))))”

@[irreducible] def forcingIdentityLiftFormula : SetTheorySemisentence 2 :=
  f“z Q. ∀ a, a ∈ z ↔ ∃ b ∈ !prod.dfn Q Q, a = !kpair.dfn b (!kpair.π₂.dfn b)”

@[irreducible] def forcingFamilyNextValueFormula : SetTheorySemisentence 5 :=
  f“z θ P Q i. (i = θ ∧ z = Q) ∨ (i ≠ θ ∧ !value.dfn z P i)”

@[irreducible] def forcingFamilyNextFormula : SetTheorySemisentence 4 :=
  f“z θ P Q. ∀ a, a ∈ z ↔ ∃ i ∈ !succ.dfn θ, a = !kpair.dfn i (!forcingFamilyNextValueFormula θ P Q i)”

@[irreducible] def forcingMatrixNextValueFormula : SetTheorySemisentence 6 :=
  f“z θ M C d a. (!kpair.π₂.dfn a = θ ∧ !forcingFamilyNextValueFormula z θ C d (!kpair.π₁.dfn a)) ∨ (!kpair.π₂.dfn a ≠ θ ∧ !value.dfn z M a)”

@[irreducible] def forcingMatrixNextFormula : SetTheorySemisentence 5 :=
  f“z θ M C d. ∀ a, a ∈ z ↔ ∃ b ∈ !prod.dfn (!succ.dfn θ) (!succ.dfn θ), a = !kpair.dfn b (!forcingMatrixNextValueFormula θ M C d b)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingCodePFormula_defined : ℒₛₑₜ-function₁[V] forcingCodeP via forcingCodePFormula :=
  ⟨fun v ↦ by simp [forcingCodePFormula, forcingCodeP]⟩

instance forcingCodeRFormula_defined : ℒₛₑₜ-function₁[V] forcingCodeR via forcingCodeRFormula :=
  ⟨fun v ↦ by simp [forcingCodeRFormula, forcingCodeR]⟩

instance forcingCodeπFormula_defined : ℒₛₑₜ-function₁[V] forcingCodeπ via forcingCodeπFormula :=
  ⟨fun v ↦ by simp [forcingCodeπFormula, forcingCodeπ]⟩

instance forcingCodeEFormula_defined : ℒₛₑₜ-function₁[V] forcingCodeE via forcingCodeEFormula :=
  ⟨fun v ↦ by simp [forcingCodeEFormula, forcingCodeE]⟩

instance forcingCodeLFormula_defined : ℒₛₑₜ-function₁[V] forcingCodeL via forcingCodeLFormula :=
  ⟨fun v ↦ by simp [forcingCodeLFormula, forcingCodeL]⟩

instance forcingCodetFormula_defined : ℒₛₑₜ-function₁[V] forcingCodet via forcingCodetFormula :=
  ⟨fun v ↦ by simp [forcingCodetFormula, forcingCodet]⟩

instance forcingIterationCodeFormula_defined : Defined (fun v : Fin 7 → V ↦ v 0 = forcingIterationCode (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) forcingIterationCodeFormula :=
  ⟨fun v ↦ by simp [forcingIterationCodeFormula, forcingIterationCode]⟩

instance forcingIdentityLiftFormula_defined : ℒₛₑₜ-function₁[V] forcingIdentityLift via forcingIdentityLiftFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [forcingIdentityLiftFormula, forcingIdentityLift, mem_definableGraph_iff]⟩

instance forcingFamilyNextValueFormula_defined : ℒₛₑₜ-function₄[V] forcingFamilyNextValue via forcingFamilyNextValueFormula :=
  ⟨fun v ↦ by classical
    by_cases h : v 4 = v 1 <;> simp [forcingFamilyNextValueFormula, forcingFamilyNextValue, h]⟩

instance forcingFamilyNextFormula_defined : ℒₛₑₜ-function₃[V] forcingFamilyNext via forcingFamilyNextFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [forcingFamilyNextFormula, forcingFamilyNext, mem_definableGraph_iff]⟩

instance forcingMatrixNextValueFormula_defined : ℒₛₑₜ-function₅[V] forcingMatrixNextValue via forcingMatrixNextValueFormula :=
  ⟨fun v ↦ by classical
    by_cases h : kpair.π₂ (v 5) = v 1 <;> simp [forcingMatrixNextValueFormula, forcingMatrixNextValue, h]⟩

instance forcingMatrixNextFormula_defined : ℒₛₑₜ-function₄[V] forcingMatrixNext via forcingMatrixNextFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [forcingMatrixNextFormula, forcingMatrixNext, mem_definableGraph_iff]⟩

end ZFVP
