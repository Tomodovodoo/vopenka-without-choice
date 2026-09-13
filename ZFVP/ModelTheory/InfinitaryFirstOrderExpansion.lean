import ZFVP.ModelTheory.InfinitarySyntax

/-! Embedded first-order formulas expand into infinitary connectives while
retaining only truth and atomic relations as embedded first-order nodes. -/

namespace ZFVP.Infinitary
open LO LO.FirstOrder

namespace Formula
variable {L : Language}

def expandFirstOrder : {n : ℕ} → Semisentence L n → Formula L n
  | _, .verum => .fo .verum
  | _, .falsum => .neg (.fo .verum)
  | _, .rel r ts => .fo (.rel r ts)
  | _, .nrel r ts => .neg (.fo (.rel r ts))
  | _, .and φ ψ => and (expandFirstOrder φ) (expandFirstOrder ψ)
  | _, .or φ ψ => or (expandFirstOrder φ) (expandFirstOrder ψ)
  | _, .all φ => all (expandFirstOrder φ)
  | _, .exs φ => .exs (expandFirstOrder φ)

@[simp] theorem eval_expandFirstOrder {M : Type*} [Structure L M]
    {n : ℕ} (φ : Semisentence L n) (b : Fin n → M) :
    Eval (expandFirstOrder φ) b ↔ φ.Evalb b := by
  induction φ with
  | verum => rfl
  | falsum => exact iff_of_eq (propext not_true)
  | rel r ts => rfl
  | nrel r ts => rfl
  | and φ ψ ihφ ihψ =>
      rw [expandFirstOrder, eval_and]
      exact and_congr (ihφ b) (ihψ b)
  | or φ ψ ihφ ihψ =>
      rw [expandFirstOrder, eval_or]
      exact or_congr (ihφ b) (ihψ b)
  | all φ ih =>
      rw [expandFirstOrder, eval_all]
      exact forall_congr' (fun x ↦ ih (x :> b))
  | exs φ ih =>
      rw [expandFirstOrder, eval_exs]
      exact exists_congr (fun x ↦ ih (x :> b))

end Formula
end ZFVP.Infinitary
