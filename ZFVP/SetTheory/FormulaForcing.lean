import ZFVP.SetTheory.ClassFormulaForcing

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingFormulaData (P R : V) {n : ℕ} (φ : SetTheorySemisentence n) :
    {F : V → V // ℒₛₑₜ-function₁ F} :=
  classForcingFormulaData P R (IsForcingName P) (by definability) φ

noncomputable def forcingFormula (P R : V) {n : ℕ} (φ : SetTheorySemisentence n) : V → V :=
  (forcingFormulaData P R φ).val

instance forcingFormula_definable (P R : V) {n : ℕ} (φ : SetTheorySemisentence n) :
    ℒₛₑₜ-function₁[V] (forcingFormula P R φ) := (forcingFormulaData P R φ).property

theorem forcingFormula_verum (P R b : V) (n : ℕ) : forcingFormula P R (.verum : SetTheorySemisentence n) b = P := rfl

theorem forcingFormula_falsum (P R b : V) (n : ℕ) : forcingFormula P R (.falsum : SetTheorySemisentence n) b = ∅ := rfl

theorem forcingFormula_rel (P R b : V) {n k : ℕ} (r : Language.Set.Rel k)
    (ts : Fin k → Semiterm ℒₛₑₜ Empty n) : forcingFormula P R (.rel r ts) b = forcingAtomic P R r ts b := rfl

theorem forcingFormula_nrel (P R b : V) {n k : ℕ} (r : Language.Set.Rel k)
    (ts : Fin k → Semiterm ℒₛₑₜ Empty n) :
    forcingFormula P R (.nrel r ts) b = forcingNegation P R (forcingAtomic P R r ts b) := rfl

theorem forcingFormula_and (P R b : V) {n : ℕ} (φ ψ : SetTheorySemisentence n) :
    forcingFormula P R (.and φ ψ) b = forcingFormula P R φ b ∩ forcingFormula P R ψ b := rfl

theorem forcingFormula_or (P R b : V) {n : ℕ} (φ ψ : SetTheorySemisentence n) :
    forcingFormula P R (.or φ ψ) b = forcingClosure P R (forcingFormula P R φ b ∪ forcingFormula P R ψ b) := rfl

theorem forcingFormula_all (P R b : V) {n : ℕ} (φ : SetTheorySemisentence (n + 1)) :
    forcingFormula P R (.all φ) b = forcingClassIntersection P (IsForcingName P) (by definability)
      (fun x ↦ forcingFormula P R φ (assignmentPrepend (n : V) b x)) (by definability) := rfl

theorem forcingFormula_exs (P R b : V) {n : ℕ} (φ : SetTheorySemisentence (n + 1)) :
    forcingFormula P R (.exs φ) b = forcingExistential P R (IsForcingName P) (by definability)
      (fun x ↦ forcingFormula P R φ (assignmentPrepend (n : V) b x)) (by definability) := rfl

theorem forcingFormula_regular {P R : V} (hR : IsForcingPreorder P R) {n : ℕ}
    (φ : SetTheorySemisentence n) (b : V) : IsForcingRegular P R (forcingFormula P R φ b) :=
  classForcingFormula_regular (IsForcingName P) (by definability) hR φ b

end ZFVP
