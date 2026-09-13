import ZFVP.Syntax.ArithmeticPrimitiveProgramEquations

/-! Explicit arithmetic routines, verified in every model of Sigma-one induction. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def identity : PrimitiveProgram := .pair .left .right

def constant : ℕ → PrimitiveProgram
  | 0 => .zero
  | n + 1 => .comp .succ (constant n)

def addition : PrimitiveProgram := .prec identity (.comp .succ (.comp .right .right))

def multiplication : PrimitiveProgram :=
  .prec .zero (.comp addition (.pair (.comp .right .right) .left))

def predecessor : PrimitiveProgram :=
  .comp (.prec .zero (.comp .left .right)) (.pair .zero identity)

def zeroTest : PrimitiveProgram :=
  .comp (.prec (constant 1) .zero) (.pair .zero identity)

def subtraction : PrimitiveProgram :=
  .prec identity (.comp predecessor (.comp .right .right))

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance evalArithmetic_definable (c : PrimitiveProgram) :
    𝚺₁.DefinableFunction₁ (c.evalArithmetic : M → M) :=
  (evalArithmetic_defined c).to_definable

@[simp] theorem evalArithmetic_identity (x : M) : identity.evalArithmetic x = x := by
  simp [identity, Arithmetic.pair_unpair]

@[simp] theorem evalArithmetic_constant (n : ℕ) (x : M) :
    (constant n).evalArithmetic x = (n : M) := by
  induction n with
  | zero => simp [constant]
  | succ n ih => simp [constant, ih, Nat.cast_succ]

@[simp] theorem evalArithmetic_addition (x y : M) :
    addition.evalArithmetic (Arithmetic.pair x y) = x + y := by
  induction y using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp [addition]
  case succ y ih =>
    rw [addition, evalArithmetic_prec_succ]
    simp only [evalArithmetic_comp, evalArithmetic_succ, evalArithmetic_right,
      Arithmetic.pi₂_pair, show (identity.prec (succ.comp (right.comp right))).evalArithmetic
        (Arithmetic.pair x y) = x + y from ih, add_assoc]

@[simp] theorem evalArithmetic_multiplication (x y : M) :
    multiplication.evalArithmetic (Arithmetic.pair x y) = x * y := by
  induction y using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp [multiplication]
  case succ y ih =>
    rw [multiplication, evalArithmetic_prec_succ]
    simp only [multiplication] at ih
    simp [ih, mul_add]

@[simp] theorem evalArithmetic_predecessor_zero : predecessor.evalArithmetic (0 : M) = 0 := by
  simp [predecessor]

@[simp] theorem evalArithmetic_predecessor_succ (x : M) :
    predecessor.evalArithmetic (x + 1) = x := by
  simp [predecessor, evalArithmetic_prec_succ]

@[simp] theorem evalArithmetic_zeroTest_zero : zeroTest.evalArithmetic (0 : M) = 1 := by
  simp [zeroTest]

@[simp] theorem evalArithmetic_zeroTest_succ (x : M) :
    zeroTest.evalArithmetic (x + 1) = 0 := by
  simp [zeroTest, evalArithmetic_prec_succ]

@[simp] theorem evalArithmetic_predecessor (x : M) : predecessor.evalArithmetic x = x - 1 := by
  rcases zero_or_succ x with (rfl | ⟨x, rfl⟩) <;> simp

@[simp] theorem evalArithmetic_subtraction (x y : M) :
    subtraction.evalArithmetic (Arithmetic.pair x y) = x - y := by
  induction y using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp [subtraction]
  case succ y ih =>
    rw [subtraction, evalArithmetic_prec_succ]
    simp only [subtraction] at ih
    simp [ih, Arithmetic.sub_sub]

@[simp] theorem evalArithmetic_zeroTest (x : M) :
    zeroTest.evalArithmetic x = if x = 0 then 1 else 0 := by
  rcases zero_or_succ x with (rfl | ⟨x, rfl⟩) <;> simp

def lessEqual : PrimitiveProgram := .comp zeroTest subtraction

def equal : PrimitiveProgram :=
  .comp zeroTest (.comp addition (.pair subtraction (.comp subtraction (.pair .right .left))))

@[simp] theorem evalArithmetic_lessEqual (x y : M) :
    lessEqual.evalArithmetic (Arithmetic.pair x y) = if x ≤ y then 1 else 0 := by
  simp [lessEqual]

@[simp] theorem evalArithmetic_equal (x y : M) :
    equal.evalArithmetic (Arithmetic.pair x y) = if x = y then 1 else 0 := by
  have h : x - y + (y - x) = 0 ↔ x = y := by
    constructor
    · intro h
      have hxy : x - y = 0 := le_antisymm (by simpa [h] using (show x - y ≤ x - y + (y - x) from le_self_add)) (Arithmetic.zero_le _)
      have hyx : y - x = 0 := by simpa [hxy] using h
      exact le_antisymm (sub_eq_zero_iff_le.mp hxy) (sub_eq_zero_iff_le.mp hyx)
    · rintro rfl
      simp
  simp [equal, h]

end PrimitiveProgram
end ZFVP
