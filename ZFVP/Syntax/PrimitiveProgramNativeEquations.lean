import ZFVP.Syntax.PrimitiveProgramNegationStandard

/-! Standard-natural equations for composing the explicit syntax programs. -/

namespace ZFVP.PrimitiveProgram

@[simp] theorem evalNat_zero (x : ℕ) : zero.eval x = 0 := rfl
@[simp] theorem evalNat_succ (x : ℕ) : succ.eval x = x + 1 := rfl
@[simp] theorem evalNat_left (x : ℕ) : left.eval x = (Nat.unpair x).1 := rfl
@[simp] theorem evalNat_right (x : ℕ) : right.eval x = (Nat.unpair x).2 := rfl
@[simp] theorem evalNat_pair (a b : PrimitiveProgram) (x : ℕ) :
    (pair a b).eval x = Nat.pair (a.eval x) (b.eval x) := rfl
@[simp] theorem evalNat_comp (a b : PrimitiveProgram) (x : ℕ) :
    (comp a b).eval x = a.eval (b.eval x) := rfl

@[simp] theorem evalNat_constant (n x : ℕ) : (constant n).eval x = n := by
  rw [← evalArithmetic_nat, evalArithmetic_constant]
  exact LO.FirstOrder.Arithmetic.natCast_nat n

@[simp] theorem evalNat_identity (x : ℕ) : identity.eval x = x := by
  rw [← evalArithmetic_nat, evalArithmetic_identity]

@[simp] theorem evalNat_tagged (t : ℕ) (a : PrimitiveProgram) (x : ℕ) :
    (tagged t a).eval x = Nat.pair t (a.eval x) + 1 := by
  simp [tagged]

@[simp] theorem evalNat_addition (x y : ℕ) : addition.eval (Nat.pair x y) = x + y := by
  rw [← evalArithmetic_nat, ← arithmeticPair_nat, evalArithmetic_addition]

end ZFVP.PrimitiveProgram
