import ZFVP.SetTheory.DeltaOneHereditarySymmetry
import ZFVP.SetTheory.DeltaOneBoundedForcing

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneForcingNameClassFormula (symmetric : Bool) : SetTheorySemisentence 4 :=
  if symmetric then sigmaOneHereditarySymmetryFormula true
  else “P Γ F τ. !sigmaOneForcingNameFormula P τ”

theorem sigmaOneForcingNameClassFormula_sigmaOne (symmetric : Bool) :
    IsSigmaFormula 1 (sigmaOneForcingNameClassFormula symmetric) := by
  cases symmetric
  · exact sigmaOneForcingNameFormula_sigmaOne.subst _
  · exact sigmaOneHereditarySymmetryFormula_sigmaOne true

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def forcingNameClass (symmetric : Bool) (P Γ F : V) : V → Prop :=
  if symmetric then IsHereditarilySymmetricName P Γ F else IsForcingName P

instance forcingNameClass_definable (symmetric : Bool) (P Γ F : V) :
    ℒₛₑₜ-predicate[V] (forcingNameClass symmetric P Γ F) := by
  cases symmetric <;> simp only [forcingNameClass, Bool.false_eq_true, reduceIte] <;> definability

theorem forcingNameClass_isName {symmetric : Bool} {P Γ F x : V} (h : forcingNameClass symmetric P Γ F x) :
    IsForcingName P x := by
  cases symmetric
  · exact h
  · exact h.1

theorem forcingNameClass_subname {symmetric : Bool} {P Γ F x u s : V}
    (h : forcingNameClass symmetric P Γ F x) (hus : ⟨u, s⟩ₖ ∈ x) : forcingNameClass symmetric P Γ F u := by
  cases symmetric
  · exact forcingName_subname h hus
  · exact hereditarilySymmetric_mem_closure h (subname_mem_nameClosure hus)

theorem eval_sigmaOneForcingNameClassFormula {P Γ : V} (hΓ : ∀ π ∈ Γ, π ∈ P ^ P)
    (symmetric : Bool) (F τ : V) : (sigmaOneForcingNameClassFormula symmetric).Evalb ![P, Γ, F, τ] ↔
      forcingNameClass symmetric P Γ F τ := by
  cases symmetric
  · simp [sigmaOneForcingNameClassFormula, forcingNameClass]
  · exact eval_sigmaOneHereditarySymmetryFormula hΓ F τ true

noncomputable def selectedForcingFormula (symmetric : Bool) (P R Γ F : V)
    {n : ℕ} (φ : SetTheorySemisentence n) : V → V :=
  classForcingFormula P R (forcingNameClass symmetric P Γ F) (by definability) φ

theorem selectedForcingFormula_ordinary (P R Γ F : V) {n : ℕ} (φ : SetTheorySemisentence n) (b : V) :
    selectedForcingFormula false P R Γ F φ b = forcingFormula P R φ b := rfl

theorem selectedForcingFormula_symmetric (P R Γ F : V) {n : ℕ} (φ : SetTheorySemisentence n) (b : V) :
    selectedForcingFormula true P R Γ F φ b = symmetricForcingFormula P R Γ F φ b := rfl

end ZFVP
