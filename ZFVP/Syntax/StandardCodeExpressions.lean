import ZFVP.Syntax.BoundedConstructorExpressions
import ZFVP.Syntax.MembershipSatisfaction

/-! Bounded constructor expressions for each externally finite membership formula. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def membershipTermIndex {n : ℕ} : SetTheorySemiterm Empty n → Fin n
  | .bvar i => i
  | .fvar e => Empty.elim e
  | .func f _ => Empty.elim f

def membershipRelationIndex : {k : ℕ} → Language.Set.Rel k → ℕ
  | _, .eq => 0
  | _, .mem => 1

def membershipArgumentExpression {n : ℕ} : {k : ℕ} → Language.Set.Rel k →
    (Fin k → SetTheorySemiterm Empty n) → CodeExpression 0
  | _, .eq, ts => .boundArgs (.num (membershipTermIndex (ts 0)).val) (.num (membershipTermIndex (ts 1)).val)
  | _, .mem, ts => .boundArgs (.num (membershipTermIndex (ts 0)).val) (.num (membershipTermIndex (ts 1)).val)

def membershipFormulaExpression {n : ℕ} : SetTheorySemisentence n → CodeExpression 0
  | .verum => .truth
  | .falsum => .falsity
  | .rel r ts => .atom (.relation (.num (membershipRelationIndex r))) (membershipArgumentExpression r ts)
  | .nrel r ts => .negAtom (.relation (.num (membershipRelationIndex r))) (membershipArgumentExpression r ts)
  | .and φ ψ => .conj (membershipFormulaExpression φ) (membershipFormulaExpression ψ)
  | .or φ ψ => .disj (membershipFormulaExpression φ) (membershipFormulaExpression ψ)
  | .all φ => .all (membershipFormulaExpression φ)
  | .exs φ => .exs (membershipFormulaExpression φ)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem encodeMembershipTerm_index {n : ℕ} (t : SetTheorySemiterm Empty n) :
    encodeSemiterm (fun {k} ↦ membershipFunctionSymbol (V := V) (k := k)) Empty.elim t =
      boundVarCode ((membershipTermIndex t).val : V) := by
  cases t with
  | bvar i => rfl
  | fvar e => exact Empty.elim e
  | func f ts => exact Empty.elim f

theorem eval_membershipArgumentExpression {n k : ℕ} (r : Language.Set.Rel k)
    (ts : Fin k → SetTheorySemiterm Empty n) :
    (membershipArgumentExpression r ts).eval (![] : Fin 0 → V) =
      standardTuple (fun i ↦ encodeSemiterm (fun {k} ↦ membershipFunctionSymbol (V := V) (k := k)) Empty.elim (ts i)) := by
  cases r <;> simp only [membershipArgumentExpression, CodeExpression.eval_boundArgs, CodeExpression.eval,
    boundPairArguments, encodeMembershipTerm_index]
  all_goals
    congr 1
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i

@[simp] theorem eval_membershipFormulaExpression {n : ℕ} (φ : SetTheorySemisentence n) :
    (membershipFormulaExpression φ).eval (![] : Fin 0 → V) = encodeMembershipFormula φ := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel r ts =>
    simp only [membershipFormulaExpression, CodeExpression.eval_atom, CodeExpression.eval_relation,
      CodeExpression.eval, eval_membershipArgumentExpression, encodeMembershipFormula, encodeSemiformula]
    cases r <;> rfl
  | nrel r ts =>
    simp only [membershipFormulaExpression, CodeExpression.eval_negAtom, CodeExpression.eval_relation,
      CodeExpression.eval, eval_membershipArgumentExpression, encodeMembershipFormula, encodeSemiformula]
    cases r <;> rfl
  | and φ ψ ihφ ihψ => simpa [membershipFormulaExpression, encodeMembershipFormula, encodeSemiformula] using congrArg₂ andCode ihφ ihψ
  | or φ ψ ihφ ihψ => simpa [membershipFormulaExpression, encodeMembershipFormula, encodeSemiformula] using congrArg₂ orCode ihφ ihψ
  | all φ ih => simpa [membershipFormulaExpression, encodeMembershipFormula, encodeSemiformula] using congrArg allCode ih
  | exs φ ih => simpa [membershipFormulaExpression, encodeMembershipFormula, encodeSemiformula] using congrArg existsCode ih

theorem eval_membershipFormulaExpression_formula {n : ℕ} (φ : SetTheorySemisentence n)
    (U x : V) [IsCodingSupport U] :
    (membershipFormulaExpression φ).formula.Evalb ![U, x] ↔ x = encodeMembershipFormula φ := by simp

end ZFVP
