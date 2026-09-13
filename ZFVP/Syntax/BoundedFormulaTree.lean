import ZFVP.SetTheory.BoundedFormulas

/-! A bounded syntax tree exposes membership bounds to the forcing translation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

inductive BoundedFormulaTree : ℕ → Type
  | verum {n} : BoundedFormulaTree n
  | falsum {n} : BoundedFormulaTree n
  | rel {n k} (r : Language.Set.Rel k) (ts : Fin k → SetTheorySemiterm Empty n) : BoundedFormulaTree n
  | nrel {n k} (r : Language.Set.Rel k) (ts : Fin k → SetTheorySemiterm Empty n) : BoundedFormulaTree n
  | and {n} (φ ψ : BoundedFormulaTree n) : BoundedFormulaTree n
  | or {n} (φ ψ : BoundedFormulaTree n) : BoundedFormulaTree n
  | all {n} (t : SetTheorySemiterm Empty n) (φ : BoundedFormulaTree (n + 1)) : BoundedFormulaTree n
  | exs {n} (t : SetTheorySemiterm Empty n) (φ : BoundedFormulaTree (n + 1)) : BoundedFormulaTree n

def BoundedFormulaTree.formula : {n : ℕ} → BoundedFormulaTree n → SetTheorySemisentence n
  | _, .verum => .verum
  | _, .falsum => .falsum
  | _, .rel r ts => .rel r ts
  | _, .nrel r ts => .nrel r ts
  | _, .and φ ψ => .and φ.formula ψ.formula
  | _, .or φ ψ => .or φ.formula ψ.formula
  | _, .all t φ => boundedSetAll t φ.formula
  | _, .exs t φ => boundedSetExs t φ.formula

theorem BoundedFormulaTree.formula_bounded {n : ℕ} (φ : BoundedFormulaTree n) : IsBoundedSetFormula φ.formula := by
  induction φ with
  | verum => exact .verum
  | falsum => exact .falsum
  | rel r ts => exact .rel r ts
  | nrel r ts => exact .nrel r ts
  | and φ ψ ihφ ihψ => exact .and ihφ ihψ
  | or φ ψ ihφ ihψ => exact .or ihφ ihψ
  | all t φ ih => exact .all t ih
  | exs t φ ih => exact .exs t ih

theorem boundedFormulaTree_exists {n : ℕ} {φ : SetTheorySemisentence n} (hφ : IsBoundedSetFormula φ) :
    ∃ t : BoundedFormulaTree n, t.formula = φ := by
  induction hφ with
  | verum => exact ⟨.verum, rfl⟩
  | falsum => exact ⟨.falsum, rfl⟩
  | rel r ts => exact ⟨.rel r ts, rfl⟩
  | nrel r ts => exact ⟨.nrel r ts, rfl⟩
  | and _ _ ihφ ihψ =>
    obtain ⟨φ, rfl⟩ := ihφ
    obtain ⟨ψ, rfl⟩ := ihψ
    exact ⟨.and φ ψ, rfl⟩
  | or _ _ ihφ ihψ =>
    obtain ⟨φ, rfl⟩ := ihφ
    obtain ⟨ψ, rfl⟩ := ihψ
    exact ⟨.or φ ψ, rfl⟩
  | all t _ ih =>
    obtain ⟨φ, rfl⟩ := ih
    exact ⟨.all t φ, rfl⟩
  | exs t _ ih =>
    obtain ⟨φ, rfl⟩ := ih
    exact ⟨.exs t φ, rfl⟩

end ZFVP
