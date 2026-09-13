import ZFVP.SetTheory.LevyComplexityBound

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Full logical constructor depth. Unlike the Levy estimate, disjunction and
conjunction each add one; class-forcing density inserts quantifiers at disjunction. -/
def formulaStructuralHeight : {n : ℕ} → SetTheorySemisentence n → ℕ
  | _, .verum | _, .falsum | _, .rel _ _ | _, .nrel _ _ => 0
  | _, .and φ ψ | _, .or φ ψ => max (formulaStructuralHeight φ) (formulaStructuralHeight ψ) + 1
  | _, .all φ | _, .exs φ => formulaStructuralHeight φ + 1

@[simp] theorem formulaStructuralHeight_neg {n} (φ : SetTheorySemisentence n) :
    formulaStructuralHeight (∼φ) = formulaStructuralHeight φ := by
  induction φ with
  | verum | falsum | rel | nrel => rfl
  | and φ ψ ihφ ihψ =>
    change max (formulaStructuralHeight φ.neg) (formulaStructuralHeight ψ.neg) + 1 = _
    simpa only [Semiformula.neg_eq, formulaStructuralHeight] using
      congrArg (· + 1) (congrArg₂ max ihφ ihψ)
  | or φ ψ ihφ ihψ =>
    change max (formulaStructuralHeight φ.neg) (formulaStructuralHeight ψ.neg) + 1 = _
    simpa only [Semiformula.neg_eq, formulaStructuralHeight] using
      congrArg (· + 1) (congrArg₂ max ihφ ihψ)
  | all φ ih =>
    change formulaStructuralHeight φ.neg + 1 = _
    simpa only [Semiformula.neg_eq, formulaStructuralHeight] using congrArg (· + 1) ih
  | exs φ ih =>
    change formulaStructuralHeight φ.neg + 1 = _
    simpa only [Semiformula.neg_eq, formulaStructuralHeight] using congrArg (· + 1) ih

@[simp] theorem formulaStructuralHeight_rew {n m} (φ : SetTheorySemisentence n)
    (σ : Rew ℒₛₑₜ Empty n Empty m) :
    formulaStructuralHeight (σ ▹ φ) = formulaStructuralHeight φ := by
  induction φ generalizing m with
  | verum | falsum | rel | nrel => rfl
  | and φ ψ ihφ ihψ => exact congrArg (· + 1) (congrArg₂ max (ihφ σ) (ihψ σ))
  | or φ ψ ihφ ihψ => exact congrArg (· + 1) (congrArg₂ max (ihφ σ) (ihψ σ))
  | all φ ih => exact congrArg (· + 1) (ih σ.q)
  | exs φ ih => exact congrArg (· + 1) (ih σ.q)

theorem levySyntacticBound_le_twice_height {n} (φ : SetTheorySemisentence n) :
    levySyntacticBound φ ≤ 2 * formulaStructuralHeight φ := by
  induction φ <;> simp_all only [levySyntacticBound, formulaStructuralHeight] <;> omega

end ZFVP
