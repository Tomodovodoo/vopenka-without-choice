import ZFVP.SetTheory.LevySubstitution

/-! Computable upper bounds for fixed formulas and finite predicate dictionaries.
These bounds count every quantifier and do not claim to be optimal. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def levySyntacticBound : {n : ℕ} → SetTheorySemisentence n → ℕ
  | _, .verum => 0
  | _, .falsum => 0
  | _, .rel _ _ => 0
  | _, .nrel _ _ => 0
  | _, .and φ ψ => max (levySyntacticBound φ) (levySyntacticBound ψ)
  | _, .or φ ψ => max (levySyntacticBound φ) (levySyntacticBound ψ)
  | _, .all φ => levySyntacticBound φ + 2
  | _, .exs φ => levySyntacticBound φ + 2

theorem isLevyFormula_syntacticBound {n : ℕ} (φ : SetTheorySemisentence n) (p : LevyPolarity) :
    IsLevyFormula p (levySyntacticBound φ) φ := by
  induction φ with
  | verum => exact .bounded .verum
  | falsum => exact .bounded .falsum
  | rel r ts => exact .bounded (.rel r ts)
  | nrel r ts => exact .bounded (.nrel r ts)
  | and φ ψ ihφ ihψ => exact .and (ihφ.mono (Nat.le_max_left _ _)) (ihψ.mono (Nat.le_max_right _ _))
  | or φ ψ ihφ ihψ => exact .or (ihφ.mono (Nat.le_max_left _ _)) (ihψ.mono (Nat.le_max_right _ _))
  | all φ ih => exact .raise (.all (.raise ih))
  | exs φ ih => exact .raise (.exs (.raise ih))

@[simp] theorem levySyntacticBound_neg {n : ℕ} (φ : SetTheorySemisentence n) :
    levySyntacticBound (∼φ) = levySyntacticBound φ := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel r ts => rfl
  | nrel r ts => rfl
  | and φ ψ ihφ ihψ =>
    change max (levySyntacticBound φ.neg) (levySyntacticBound ψ.neg) = _
    simpa only [Semiformula.neg_eq, levySyntacticBound] using congrArg₂ max ihφ ihψ
  | or φ ψ ihφ ihψ =>
    change max (levySyntacticBound φ.neg) (levySyntacticBound ψ.neg) = _
    simpa only [Semiformula.neg_eq, levySyntacticBound] using congrArg₂ max ihφ ihψ
  | all φ ih =>
    change levySyntacticBound φ.neg + 2 = _
    simpa only [Semiformula.neg_eq, levySyntacticBound] using congrArg (fun n ↦ n + 2) ih
  | exs φ ih =>
    change levySyntacticBound φ.neg + 2 = _
    simpa only [Semiformula.neg_eq, levySyntacticBound] using congrArg (fun n ↦ n + 2) ih

@[simp] theorem levySyntacticBound_rew {n m : ℕ} (φ : SetTheorySemisentence n)
    (σ : Rew ℒₛₑₜ Empty n Empty m) : levySyntacticBound (σ ▹ φ) = levySyntacticBound φ := by
  induction φ generalizing m with
  | verum => rfl
  | falsum => rfl
  | rel r ts => rfl
  | nrel r ts => rfl
  | and φ ψ ihφ ihψ => exact congrArg₂ max (ihφ σ) (ihψ σ)
  | or φ ψ ihφ ihψ => exact congrArg₂ max (ihφ σ) (ihψ σ)
  | all φ ih => exact congrArg (fun n ↦ n + 2) (ih σ.q)
  | exs φ ih => exact congrArg (fun n ↦ n + 2) (ih σ.q)

abbrev SetFormulaDictionary := List (Σ n : ℕ, SetTheorySemisentence n)

def levyDictionaryBound : SetFormulaDictionary → ℕ
  | [] => 0
  | φ :: Φ => max (levySyntacticBound φ.2) (levyDictionaryBound Φ)

theorem levyDictionaryBound_append (Φ Ψ : SetFormulaDictionary) :
    levyDictionaryBound (Φ ++ Ψ) = max (levyDictionaryBound Φ) (levyDictionaryBound Ψ) := by
  induction Φ with
  | nil => simp [levyDictionaryBound]
  | cons φ Φ ih => simp [levyDictionaryBound, ih, Nat.max_assoc]

theorem levySyntacticBound_le_dictionaryBound (Φ : SetFormulaDictionary) :
    ∀ φ ∈ Φ, levySyntacticBound φ.2 ≤ levyDictionaryBound Φ := by
  induction Φ with
  | nil => simp
  | cons ψ Φ ih =>
    intro φ hφ
    rcases List.mem_cons.mp hφ with rfl | hφ
    · exact Nat.le_max_left _ _
    · exact (ih φ hφ).trans (Nat.le_max_right _ _)

theorem isLevyFormula_dictionaryBound {n : ℕ} {φ : SetTheorySemisentence n}
    (Φ : SetFormulaDictionary) (hφ : ⟨n, φ⟩ ∈ Φ) (p : LevyPolarity) :
    IsLevyFormula p (levyDictionaryBound Φ) φ :=
  (isLevyFormula_syntacticBound φ p).mono (levySyntacticBound_le_dictionaryBound Φ _ hφ)

theorem isLevyFormula_dictionary_substitution {n m : ℕ} {φ : SetTheorySemisentence n}
    (Φ : SetFormulaDictionary) (hφ : ⟨n, φ⟩ ∈ Φ) (p : LevyPolarity)
    (ts : Fin n → SetTheorySemiterm Empty m) :
    IsLevyFormula p (levyDictionaryBound Φ) (φ.subst ts) :=
  (isLevyFormula_dictionaryBound Φ hφ p).subst ts

end ZFVP
