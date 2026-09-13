import ZFVP.SetTheory.UniformRecursion

/-! Uniform recursion with one carried parameter. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def parameterAttemptFormula (φ : SetTheorySemisentence 3) : SetTheorySemisentence 3 :=
  f“a α f. !IsOrdinal.dfn α ∧ !IsFunction.dfn f ∧ α = !domain.dfn f ∧
    ∀ β ∈ α, ∀ y, !kpair.dfn β y ∈ f ↔ !φ y a (!restrict.dfn f β)”

def parameterRecursionFormula (φ : SetTheorySemisentence 3) : SetTheorySemisentence 3 :=
  “y a α. (∃ f, !(parameterAttemptFormula φ) a α f ∧ !φ y a f) ∨
    (¬!IsOrdinal.dfn α ∧ !isEmpty y)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def parameterRecursion (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (a α : V) : V :=
  Replacement.transfiniteRec (F a) (by definability) α

instance parameterAttemptFormula_defined (F : V → V → V) (φ : SetTheorySemisentence 3)
    [hF : ℒₛₑₜ-function₂ F via φ] :
    ℒₛₑₜ-relation₃ (fun a α f ↦ IsAttempt (F a) α f) via parameterAttemptFormula φ :=
  ⟨fun v ↦ by simp [parameterAttemptFormula, IsAttempt, eq_comm]⟩

instance parameterRecursionFormula_defined (F : V → V → V) (φ : SetTheorySemisentence 3)
    [hF : ℒₛₑₜ-function₂ F via φ] :
    ℒₛₑₜ-function₂ (parameterRecursion F hF.to_definable) via parameterRecursionFormula φ :=
  ⟨fun v ↦ by simp [parameterRecursionFormula, parameterRecursion,
    transfiniteRec_eq_iff, isEmpty_iff_eq_empty]⟩

end ZFVP
