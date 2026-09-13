import ZFVP.SetTheory.SymmetricFormulaForcing
import ZFVP.SetTheory.FormulaForcing

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem classForcingFormula_exs_dense_iff (P R : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N)
    {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (b p : V) :
    p ∈ classForcingFormula P R N hN (.exs φ) b ↔
      p ∈ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧
        ∃ ν, N ν ∧ r ∈ classForcingFormula P R N hN φ (assignmentPrepend (n : V) b ν) := by
  rw [classForcingFormula_exs, forcingExistential, mem_forcingClosure_iff]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro q
  apply forall_congr'
  intro _
  apply forall_congr'
  intro _
  constructor
  · rintro ⟨r, hr, hrq⟩
    obtain ⟨hrP, ν, hν, hrF⟩ := (mem_forcingClassUnion_iff _ _ _ _ _ _).mp hr
    exact ⟨r, hrP, hrq, ν, hν, hrF⟩
  · rintro ⟨r, hrP, hrq, ν, hν, hrF⟩
    exact ⟨r, (mem_forcingClassUnion_iff _ _ _ _ _ _).mpr ⟨hrP, ν, hν, hrF⟩, hrq⟩

theorem forcingFormula_exs_dense_iff (P R : V) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1)) (b p : V) :
    p ∈ forcingFormula P R (.exs φ) b ↔
      p ∈ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧
        ∃ ν, IsForcingName P ν ∧ r ∈ forcingFormula P R φ (assignmentPrepend (n : V) b ν) :=
  classForcingFormula_exs_dense_iff P R (IsForcingName P) (by definability) φ b p

theorem symmetricForcingFormula_exs_dense_iff (P R Γ F : V) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1)) (b p : V) :
    p ∈ symmetricForcingFormula P R Γ F (.exs φ) b ↔
      p ∈ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧
        ∃ ν, IsHereditarilySymmetricName P Γ F ν ∧
          r ∈ symmetricForcingFormula P R Γ F φ (assignmentPrepend (n : V) b ν) :=
  classForcingFormula_exs_dense_iff P R (IsHereditarilySymmetricName P Γ F) (by definability) φ b p

theorem symmetricForcingFormula_rel_eq_ordinary (P R Γ F b : V) {n k : ℕ}
    (r : Language.Set.Rel k) (ts : Fin k → Semiterm ℒₛₑₜ Empty n) :
    symmetricForcingFormula P R Γ F (.rel r ts) b = forcingFormula P R (.rel r ts) b := rfl

theorem symmetricForcingFormula_nrel_eq_ordinary (P R Γ F b : V) {n k : ℕ}
    (r : Language.Set.Rel k) (ts : Fin k → Semiterm ℒₛₑₜ Empty n) :
    symmetricForcingFormula P R Γ F (.nrel r ts) b = forcingFormula P R (.nrel r ts) b := rfl

end ZFVP
