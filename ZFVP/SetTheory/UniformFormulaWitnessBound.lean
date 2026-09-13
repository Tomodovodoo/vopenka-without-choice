import ZFVP.ModelTheory.ForcingFormulaName
import ZFVP.SetTheory.TwoStepForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def formulaOutputTruthFormula {n : ℕ} (φ : SetTheorySemisentence (n + 1)) : SetTheorySemisentence 5 :=
  f“P R a ν p. !(forcingTruthFormula φ) p P R
    (!assignmentPrependFormula (!(numeralFormula n)) a ν)”

def formulaWitnessBoundProperty {n : ℕ} (φ : SetTheorySemisentence (n + 1)) : SetTheorySemisentence 4 :=
  f“P R a α. ∀ p ∈ P, (∃ ν, !forcingNameFormula P ν ∧ !(formulaOutputTruthFormula φ) P R a ν p) →
    ∃ ν ∈ (!hierarchyFormula α), !forcingNameFormula P ν ∧ !(formulaOutputTruthFormula φ) P R a ν p”

def formulaWitnessBoundFormula {n : ℕ} (φ : SetTheorySemisentence (n + 1)) : SetTheorySemisentence 4 :=
  f“α P R a. !IsOrdinal.dfn α ∧ !(formulaWitnessBoundProperty φ) P R a α ∧
    ∀ β, !IsOrdinal.dfn β → !(formulaWitnessBoundProperty φ) P R a β → α ⊆ β”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance formulaOutputTruthFormula_defined {n : ℕ} (φ : SetTheorySemisentence (n + 1)) :
    Defined (fun v : Fin 5 → V ↦ v 4 ∈ forcingFormula (v 0) (v 1) φ
      (assignmentPrepend (n : V) (v 2) (v 3))) (formulaOutputTruthFormula φ) :=
  ⟨fun v ↦ by simp [formulaOutputTruthFormula]⟩

instance formulaWitnessBoundProperty_defined {n : ℕ} (φ : SetTheorySemisentence (n + 1)) :
    Defined (fun v : Fin 4 → V ↦ IsForcingWitnessBound (v 0)
      (fun a ν ↦ forcingFormula (v 0) (v 1) φ (assignmentPrepend (n : V) a ν)) (v 2) (v 3))
      (formulaWitnessBoundProperty φ) :=
  ⟨fun v ↦ by simp [formulaWitnessBoundProperty, IsForcingWitnessBound]⟩

instance formulaWitnessBoundFormula_defined {n : ℕ} (φ : SetTheorySemisentence (n + 1)) :
    Defined (fun v : Fin 4 → V ↦ v 0 = forcingWitnessBound (v 1)
      (fun a ν ↦ forcingFormula (v 1) (v 2) φ (assignmentPrepend (n : V) a ν))
      (by definability) (v 3)) (formulaWitnessBoundFormula φ) := by
  refine ⟨fun v ↦ ?_⟩
  let F := fun a ν ↦ forcingFormula (v 1) (v 2) φ (assignmentPrepend (n : V) a ν)
  have hF : ℒₛₑₜ-function₂ F := by unfold F; definability
  have ht : (formulaWitnessBoundFormula φ).Evalb v ↔
      IsLeastOrdinal (IsForcingWitnessBound (v 1) F (v 3)) (v 0) := by
    simp [formulaWitnessBoundFormula, IsLeastOrdinal, F]
  rw [ht]
  have hs := leastOrdinalOrZero_spec (IsForcingWitnessBound (v 1) F)
    (forcingWitnessBound_definable (v 1) F hF) (v 3) (forcingWitnessBound_exists (v 1) F hF (v 3))
  constructor
  · intro hv
    exact (leastOrdinal_existsUnique _ (by
      have := forcingWitnessBound_definable (v 1) F hF
      definability) (forcingWitnessBound_exists (v 1) F hF (v 3))).unique hv hs
  · intro he
    rw [he]
    exact hs

end ZFVP
