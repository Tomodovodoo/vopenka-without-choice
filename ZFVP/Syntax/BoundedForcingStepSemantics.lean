import ZFVP.Syntax.BoundedForcingSteps
import ZFVP.SetTheory.ClassForcingBounded

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_and {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → V) :
    (φ.and ψ).Evalb v ↔ φ.Evalb v ∧ ψ.Evalb v := Iff.rfl

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_or {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → V) :
    (φ.or ψ).Evalb v ↔ φ.Evalb v ∨ ψ.Evalb v := Iff.rfl

theorem forcingTermValue_standard {n : ℕ} (t : SetTheorySemiterm Empty n) (v : Fin n → V) :
    forcingTermValue t (standardTuple v) = t.val v Empty.elim := by
  cases t with
  | bvar i => exact value_standardTuple v i
  | fvar x => exact Empty.elim x
  | func f _ => exact Empty.elim f

theorem eval_forcingAtomicSigmaStep {n k : ℕ} (r : Language.Set.Rel k)
    (ts : Fin k → SetTheorySemiterm Empty n) (answer : Bool) (T P R p : V) (v : Fin n → V) :
    (forcingAtomicSigmaStep r ts answer).Evalb (T :> P :> R :> p :> v) ↔
      TruthAnswer answer (p ∈ forcingAtomic P R r ts (standardTuple v)) := by
  cases r <;> simp [forcingAtomicSigmaStep, Semiformula.eval_substs, Semiterm.val_substs,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, forcingParameterTerms,
    forcingAtomic, forcingTermValue_standard]

theorem eval_forcingNegationSigmaStep {n : ℕ} (φ : SetTheorySemisentence (n + 4))
    (answer : Bool) (T P R p : V) (v : Fin n → V) :
    (forcingNegationSigmaStep φ answer).Evalb (T :> P :> R :> p :> v) ↔
      if answer then p ∈ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → φ.Evalb (T :> P :> R :> q :> v)
      else p ∉ P ∨ ∃ q ∈ P, ⟨q, p⟩ₖ ∈ R ∧ φ.Evalb (T :> P :> R :> q :> v) := by
  cases answer <;> simp [forcingNegationSigmaStep, eval_and, eval_or, eval_boundedSetAll, eval_boundedSetExs,
    forcingContextSubst, Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton,
    Function.comp_def, forcingParameterTerms, Structure.rel, ← imp_iff_not_or]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_forcingAndSigmaStep {n : ℕ} (φ ψ : SetTheorySemisentence (n + 4))
    (answer : Bool) (T P R p : V) (v : Fin n → V) :
    (forcingAndSigmaStep φ ψ answer).Evalb (T :> P :> R :> p :> v) ↔
      if answer then φ.Evalb (T :> P :> R :> p :> v) ∧ ψ.Evalb (T :> P :> R :> p :> v)
      else φ.Evalb (T :> P :> R :> p :> v) ∨ ψ.Evalb (T :> P :> R :> p :> v) := by
  cases answer <;> rfl

theorem eval_forcingOrSigmaStep {n : ℕ} (φ ψ : SetTheorySemisentence (n + 4))
    (answer : Bool) (T P R p : V) (v : Fin n → V) :
    (forcingOrSigmaStep φ ψ answer).Evalb (T :> P :> R :> p :> v) ↔
      if answer then p ∈ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧
        (φ.Evalb (T :> P :> R :> r :> v) ∨ ψ.Evalb (T :> P :> R :> r :> v))
      else p ∉ P ∨ ∃ q ∈ P, ⟨q, p⟩ₖ ∈ R ∧ ∀ r ∈ P, ⟨r, q⟩ₖ ∈ R →
        φ.Evalb (T :> P :> R :> r :> v) ∧ ψ.Evalb (T :> P :> R :> r :> v) := by
  cases answer <;> simp [forcingOrSigmaStep, eval_and, eval_or, eval_boundedSetAll, eval_boundedSetExs,
    forcingContextSubst, Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton,
    Function.comp_def, forcingParameterTerms, Structure.rel, ← imp_iff_not_or]

theorem eval_forcingAllSigmaStep {n : ℕ} (t : SetTheorySemiterm Empty n)
    (φ : SetTheorySemisentence (n + 1 + 4)) (answer : Bool) (T P R p : V) (v : Fin n → V) :
    (forcingAllSigmaStep t φ answer).Evalb (T :> P :> R :> p :> v) ↔
      if answer then p ∈ P ∧ ∀ u ∈ T, ∀ s ∈ T, ⟨u, s⟩ₖ ∈ t.val v Empty.elim →
        ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ⟨q, s⟩ₖ ∈ R → φ.Evalb (T :> P :> R :> q :> u :> v)
      else p ∉ P ∨ ∃ u ∈ T, ∃ s ∈ T, ⟨u, s⟩ₖ ∈ t.val v Empty.elim ∧
        ∃ q ∈ P, ⟨q, p⟩ₖ ∈ R ∧ ⟨q, s⟩ₖ ∈ R ∧ φ.Evalb (T :> P :> R :> q :> u :> v) := by
  cases answer <;> simp [forcingAllSigmaStep, eval_and, eval_or, eval_boundedSetAll, eval_boundedSetExs,
    forcingContextSubst, Semiformula.eval_substs, Semiterm.val_substs,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, forcingParameterTerms,
    Structure.rel, ← imp_iff_not_or]

theorem eval_forcingExsSigmaStep {n : ℕ} (t : SetTheorySemiterm Empty n)
    (φ : SetTheorySemisentence (n + 1 + 4)) (answer : Bool) (T P R p : V) (v : Fin n → V) :
    (forcingExsSigmaStep t φ answer).Evalb (T :> P :> R :> p :> v) ↔
      if answer then p ∈ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧
        ∃ u ∈ T, ∃ s ∈ T, ⟨u, s⟩ₖ ∈ t.val v Empty.elim ∧ ⟨r, s⟩ₖ ∈ R ∧
          φ.Evalb (T :> P :> R :> r :> u :> v)
      else p ∉ P ∨ ∃ q ∈ P, ⟨q, p⟩ₖ ∈ R ∧ ∀ r ∈ P, ⟨r, q⟩ₖ ∈ R →
        ∀ u ∈ T, ∀ s ∈ T, ⟨u, s⟩ₖ ∈ t.val v Empty.elim → ⟨r, s⟩ₖ ∈ R →
          φ.Evalb (T :> P :> R :> r :> u :> v) := by
  cases answer <;> simp [forcingExsSigmaStep, eval_and, eval_or, eval_boundedSetAll, eval_boundedSetExs,
    forcingContextSubst, Semiformula.eval_substs, Semiterm.val_substs,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, forcingParameterTerms,
    Structure.rel, ← imp_iff_not_or]

end ZFVP
