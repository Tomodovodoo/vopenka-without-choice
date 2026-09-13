import ZFVP.SetTheory.SigmaOneNameStabilizer
import ZFVP.SetTheory.DeltaOneForcingNames

/-! Hereditary symmetry has Sigma_1 and Pi_1 definitions for families of
condition functions. In particular this applies to every symmetric system. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def hereditarySymmetryBodyFormula (answer : Bool) : SetTheorySemisentence 4 :=
  if answer then “P Γ F C. ∀ u ∈ C, ∃ H, !sigmaOneNameStabilizerFormula P Γ u H ∧ H ∈ F”
  else “P Γ F C. ∃ u ∈ C, ∃ H, !sigmaOneNameStabilizerFormula P Γ u H ∧ H ∉ F”

def hereditarySymmetryCertificateFormula (answer : Bool) : SetTheorySemisentence 4 :=
  “P Γ F τ. ∃ C, !sigmaOneNameClosureFormula C τ ∧ !(hereditarySymmetryBodyFormula answer) P Γ F C”

def sigmaOneHereditarySymmetryFormula (answer : Bool) : SetTheorySemisentence 4 :=
  if answer then “P Γ F τ. !sigmaOneForcingNameFormula P τ ∧ !(hereditarySymmetryCertificateFormula true) P Γ F τ”
  else “P Γ F τ. !sigmaOneNonForcingNameFormula P τ ∨
    (!sigmaOneForcingNameFormula P τ ∧ !(hereditarySymmetryCertificateFormula false) P Γ F τ)”

def piOneHereditarySymmetryFormula : SetTheorySemisentence 4 := ∼sigmaOneHereditarySymmetryFormula false

theorem hereditarySymmetryBodyFormula_sigmaOne (answer : Bool) : IsSigmaFormula 1 (hereditarySymmetryBodyFormula answer) := by
  cases answer
  · exact .boundedExs (.bvar 3) (.exs (.and (sigmaOneNameStabilizerFormula_sigmaOne.subst _) (.bounded (.nrel _ _))))
  · exact .boundedAll (.bvar 3) (.exs (.and (sigmaOneNameStabilizerFormula_sigmaOne.subst _) (.bounded (.rel _ _))))

theorem hereditarySymmetryCertificateFormula_sigmaOne (answer : Bool) :
    IsSigmaFormula 1 (hereditarySymmetryCertificateFormula answer) :=
  .exs (.and (sigmaOneNameClosureFormula_sigmaOne.subst _) ((hereditarySymmetryBodyFormula_sigmaOne answer).subst _))

theorem sigmaOneHereditarySymmetryFormula_sigmaOne (answer : Bool) :
    IsSigmaFormula 1 (sigmaOneHereditarySymmetryFormula answer) := by
  cases answer
  · exact .or (sigmaOneNonForcingNameFormula_sigmaOne.subst _) (.and (sigmaOneForcingNameFormula_sigmaOne.subst _)
      ((hereditarySymmetryCertificateFormula_sigmaOne false).subst _))
  · exact .and (sigmaOneForcingNameFormula_sigmaOne.subst _) ((hereditarySymmetryCertificateFormula_sigmaOne true).subst _)

theorem piOneHereditarySymmetryFormula_piOne : IsPiFormula 1 piOneHereditarySymmetryFormula :=
  (sigmaOneHereditarySymmetryFormula_sigmaOne false).neg

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_hereditarySymmetryBodyFormula {P Γ τ : V} (hΓ : ∀ π ∈ Γ, π ∈ P ^ P)
    (hτ : IsForcingName P τ) (F : V) (answer : Bool) :
    (hereditarySymmetryBodyFormula answer).Evalb ![P, Γ, F, nameClosure τ] ↔
      TruthAnswer answer (∀ u ∈ nameClosure τ, nameStabilizer Γ u ∈ F) := by
  have he (u : V) (hu : u ∈ nameClosure τ) (H : V) :=
    eval_sigmaOneNameStabilizerFormula hΓ (forcingName_mem_closure hτ hu) H
  cases answer
  · simp only [hereditarySymmetryBodyFormula, Bool.false_eq_true, reduceIte]
    simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, TruthAnswer]
    apply exists_congr
    intro u
    apply and_congr_right
    intro hu
    simp only [he u hu]
    simp
  · simp only [hereditarySymmetryBodyFormula, reduceIte]
    simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, TruthAnswer]
    apply forall_congr'
    intro u
    apply imp_congr_right
    intro hu
    simp only [he u hu]
    simp

theorem eval_hereditarySymmetryCertificateFormula {P Γ τ : V} (hΓ : ∀ π ∈ Γ, π ∈ P ^ P)
    (hτ : IsForcingName P τ) (F : V) (answer : Bool) :
    (hereditarySymmetryCertificateFormula answer).Evalb ![P, Γ, F, τ] ↔
      TruthAnswer answer (∀ u ∈ nameClosure τ, nameStabilizer Γ u ∈ F) := by
  simp [hereditarySymmetryCertificateFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, eval_hereditarySymmetryBodyFormula hΓ hτ]

theorem eval_sigmaOneHereditarySymmetryFormula {P Γ : V} (hΓ : ∀ π ∈ Γ, π ∈ P ^ P)
    (F τ : V) (answer : Bool) : (sigmaOneHereditarySymmetryFormula answer).Evalb ![P, Γ, F, τ] ↔
      TruthAnswer answer (IsHereditarilySymmetricName P Γ F τ) := by
  by_cases hτ : IsForcingName P τ
  · cases answer <;> simp [sigmaOneHereditarySymmetryFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, eval_hereditarySymmetryCertificateFormula hΓ hτ,
      eval_sigmaOneNonForcingNameFormula, IsHereditarilySymmetricName, TruthAnswer, hτ]
  · cases answer <;> simp [sigmaOneHereditarySymmetryFormula, eval_sigmaOneNonForcingNameFormula,
      IsHereditarilySymmetricName, TruthAnswer, hτ]

theorem eval_piOneHereditarySymmetryFormula {P Γ : V} (hΓ : ∀ π ∈ Γ, π ∈ P ^ P) (F τ : V) :
    piOneHereditarySymmetryFormula.Evalb ![P, Γ, F, τ] ↔ IsHereditarilySymmetricName P Γ F τ := by
  simp [piOneHereditarySymmetryFormula, eval_sigmaOneHereditarySymmetryFormula hΓ, TruthAnswer]

end ZFVP
