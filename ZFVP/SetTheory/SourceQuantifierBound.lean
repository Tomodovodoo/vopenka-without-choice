import ZFVP.SetTheory.LevyComplexityBound

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- The paper's q: every quantifier in the expanded membership-language AST,
including membership-guarded quantifiers, is counted. -/
def sourceQuantifierCount : {n : ℕ} → SetTheorySemisentence n → ℕ
  | _, .verum | _, .falsum | _, .rel _ _ | _, .nrel _ _ => 0
  | _, .and φ ψ | _, .or φ ψ => sourceQuantifierCount φ + sourceQuantifierCount ψ
  | _, .all φ | _, .exs φ => sourceQuantifierCount φ + 1

@[simp] theorem sourceQuantifierCount_neg {n} (φ : SetTheorySemisentence n) :
    sourceQuantifierCount (∼φ) = sourceQuantifierCount φ := by
  induction φ with
  | verum | falsum | rel | nrel => rfl
  | and φ ψ ihφ ihψ =>
    change sourceQuantifierCount φ.neg + sourceQuantifierCount ψ.neg = _
    simpa only [Semiformula.neg_eq, sourceQuantifierCount] using congrArg₂ (· + ·) ihφ ihψ
  | or φ ψ ihφ ihψ =>
    change sourceQuantifierCount φ.neg + sourceQuantifierCount ψ.neg = _
    simpa only [Semiformula.neg_eq, sourceQuantifierCount] using congrArg₂ (· + ·) ihφ ihψ
  | all φ ih =>
    change sourceQuantifierCount φ.neg + 1 = _
    simpa only [Semiformula.neg_eq, sourceQuantifierCount] using congrArg (· + 1) ih
  | exs φ ih =>
    change sourceQuantifierCount φ.neg + 1 = _
    simpa only [Semiformula.neg_eq, sourceQuantifierCount] using congrArg (· + 1) ih

@[simp] theorem sourceQuantifierCount_rew {n m} (φ : SetTheorySemisentence n)
    (σ : Rew ℒₛₑₜ Empty n Empty m) :
    sourceQuantifierCount (σ ▹ φ) = sourceQuantifierCount φ := by
  induction φ generalizing m with
  | verum | falsum | rel | nrel => rfl
  | and φ ψ ihφ ihψ => exact congrArg₂ (· + ·) (ihφ σ) (ihψ σ)
  | or φ ψ ihφ ihψ => exact congrArg₂ (· + ·) (ihφ σ) (ihψ σ)
  | all φ ih => exact congrArg (· + 1) (ih σ.q)
  | exs φ ih => exact congrArg (· + 1) (ih σ.q)

/-- Maximum q over the subformula-and-negation closure of one formula.
Negation preserves q, so both polarities are included by the same entry. -/
def sourceSubformulaMax : {n : ℕ} → SetTheorySemisentence n → ℕ
  | _, .verum | _, .falsum | _, .rel _ _ | _, .nrel _ _ => 0
  | _, .and φ ψ => max (sourceQuantifierCount (.and φ ψ))
      (max (sourceSubformulaMax φ) (sourceSubformulaMax ψ))
  | _, .or φ ψ => max (sourceQuantifierCount (.or φ ψ))
      (max (sourceSubformulaMax φ) (sourceSubformulaMax ψ))
  | _, .all φ => max (sourceQuantifierCount (.all φ)) (sourceSubformulaMax φ)
  | _, .exs φ => max (sourceQuantifierCount (.exs φ)) (sourceSubformulaMax φ)

theorem sourceSubformulaMax_eq {n} (φ : SetTheorySemisentence n) :
    sourceSubformulaMax φ = sourceQuantifierCount φ := by
  induction φ <;> simp_all [sourceSubformulaMax, sourceQuantifierCount]

/-- Literal c_D({e}) after predicate elimination: ell=q+1, then 2+max ell
over the subformula-and-negation closure. -/
def sourceSingletonBound {n} (expanded : SetTheorySemisentence n) : ℕ :=
  2 + (sourceSubformulaMax expanded + 1)

theorem sourceSingletonBound_eq {n} (φ : SetTheorySemisentence n) :
    sourceSingletonBound φ = sourceQuantifierCount φ + 3 := by
  simp [sourceSingletonBound, sourceSubformulaMax_eq]; omega

/-- The paper's ell bounds both polarities directly; no factor-two estimate. -/
theorem isLevyFormula_sourceQuantifierCount {n} (φ : SetTheorySemisentence n) :
    ∀ p, IsLevyFormula p (sourceQuantifierCount φ + 1) φ := by
  induction φ with
  | verum => intro p; exact .bounded .verum
  | falsum => intro p; exact .bounded .falsum
  | rel r ts => intro p; exact .bounded (.rel r ts)
  | nrel r ts => intro p; exact .bounded (.nrel r ts)
  | and φ ψ ihφ ihψ =>
    intro p
    exact .and ((ihφ p).mono (by simp only [sourceQuantifierCount]; omega))
      ((ihψ p).mono (by simp only [sourceQuantifierCount]; omega))
  | or φ ψ ihφ ihψ =>
    intro p
    exact .or ((ihφ p).mono (by simp only [sourceQuantifierCount]; omega))
      ((ihψ p).mono (by simp only [sourceQuantifierCount]; omega))
  | all φ ih => intro p; exact .raise (.all (ih .pi))
  | exs φ ih => intro p; exact .raise (.exs (ih .sigma))

end ZFVP
