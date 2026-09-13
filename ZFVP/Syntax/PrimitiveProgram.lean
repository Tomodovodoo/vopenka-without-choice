import Mathlib.Computability.Primrec.Basic

/-! Explicit programs for mathlib's primitive-recursive natural-number functions. -/

namespace ZFVP

inductive PrimitiveProgram
  | zero
  | succ
  | left
  | right
  | pair : PrimitiveProgram → PrimitiveProgram → PrimitiveProgram
  | comp : PrimitiveProgram → PrimitiveProgram → PrimitiveProgram
  | prec : PrimitiveProgram → PrimitiveProgram → PrimitiveProgram

namespace PrimitiveProgram

def eval : PrimitiveProgram → ℕ → ℕ
  | .zero => fun _ ↦ 0
  | .succ => Nat.succ
  | .left => fun n ↦ (Nat.unpair n).1
  | .right => fun n ↦ (Nat.unpair n).2
  | .pair a b => fun n ↦ Nat.pair (a.eval n) (b.eval n)
  | .comp a b => fun n ↦ a.eval (b.eval n)
  | .prec a b => Nat.unpaired fun z n ↦ Nat.rec (a.eval z) (fun y r ↦ b.eval (Nat.pair z (Nat.pair y r))) n

theorem eval_primrec (c : PrimitiveProgram) : Nat.Primrec c.eval := by
  induction c with
  | zero => exact .zero
  | succ => exact .succ
  | left => exact .left
  | right => exact .right
  | pair a b ha hb => exact .pair ha hb
  | comp a b ha hb =>
    change Nat.Primrec (fun n ↦ a.eval (b.eval n))
    exact .comp ha hb
  | prec a b ha hb => exact .prec ha hb

theorem exists_of_primrec {f : ℕ → ℕ} (hf : Nat.Primrec f) : ∃ c : PrimitiveProgram, c.eval = f := by
  induction hf with
  | zero => exact ⟨.zero, rfl⟩
  | succ => exact ⟨.succ, rfl⟩
  | left => exact ⟨.left, rfl⟩
  | right => exact ⟨.right, rfl⟩
  | pair _ _ ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨.pair a b, rfl⟩
  | comp _ _ ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨.comp a b, rfl⟩
  | prec _ _ ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨.prec a b, rfl⟩

theorem exists_eval_iff (f : ℕ → ℕ) : (∃ c : PrimitiveProgram, c.eval = f) ↔ Nat.Primrec f := by
  constructor
  · rintro ⟨c, rfl⟩
    exact c.eval_primrec
  · exact exists_of_primrec

end PrimitiveProgram
end ZFVP
