import ZFVP.Syntax.ArithmeticPrimitiveProgramEquations

/-! Standard-natural-number correctness of the arithmetic program formulas. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

theorem arithmeticPair_nat (m n : ℕ) : Arithmetic.pair m n = Nat.pair m n := by
  classical
  unfold Arithmetic.pair Nat.pair
  split_ifs <;> rfl

theorem arithmeticUnpair_nat (n : ℕ) : Arithmetic.unpair n = Nat.unpair n := by
  have h := Arithmetic.unpair_pair (Nat.unpair n).1 (Nat.unpair n).2
  rw [arithmeticPair_nat, Nat.pair_unpair] at h
  exact h

namespace PrimitiveProgram

theorem evalArithmetic_nat (c : PrimitiveProgram) (n : ℕ) : c.evalArithmetic n = c.eval n := by
  induction c generalizing n with
  | zero => rfl
  | succ => rfl
  | left => exact congrArg Prod.fst (arithmeticUnpair_nat n)
  | right => exact congrArg Prod.snd (arithmeticUnpair_nat n)
  | pair a b ha hb =>
    rw [evalArithmetic_pair, ha, hb, arithmeticPair_nat]
    rfl
  | comp a b ha hb =>
    rw [evalArithmetic_comp, ha, hb]
    rfl
  | prec a b ha hb =>
    have hr (z k : ℕ) : (PrimitiveProgram.prec a b).evalArithmetic (Nat.pair z k) =
        Nat.rec (a.eval z) (fun y r ↦ b.eval (Nat.pair z (Nat.pair y r))) k := by
      induction k with
      | zero =>
        rw [← arithmeticPair_nat, evalArithmetic_prec_zero, ha]
        rfl
      | succ k ih =>
        rw [← arithmeticPair_nat, evalArithmetic_prec_succ, hb,
          arithmeticPair_nat, arithmeticPair_nat, arithmeticPair_nat, ih]
    simpa only [Nat.pair_unpair, eval, Nat.unpaired] using hr (Nat.unpair n).1 (Nat.unpair n).2

theorem eval_arithmeticFormula_nat (c : PrimitiveProgram) (x y : ℕ) :
    c.arithmeticFormula.val.Evalb ![y, x] ↔ y = c.eval x := by
  rw [eval_arithmeticFormula_iff, evalArithmetic_nat]

end PrimitiveProgram
end ZFVP
