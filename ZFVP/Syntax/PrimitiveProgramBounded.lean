import ZFVP.Syntax.PrimitiveProgramArithmetic

/-! Explicit branching and bounded universal tests for primitive-recursive programs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def ifZero (test yes no : PrimitiveProgram) : PrimitiveProgram :=
  .comp (.prec yes (.comp no .left)) (.pair identity test)

def nonzeroTest : PrimitiveProgram := .comp zeroTest zeroTest

def boundedAll (test : PrimitiveProgram) : PrimitiveProgram :=
  .prec (constant 1) (.comp multiplication (.pair (.comp .right .right)
    (.comp nonzeroTest (.comp test (.pair .left (.comp .left .right))))))

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem evalArithmetic_ifZero (test yes no : PrimitiveProgram) (x : M) :
    (ifZero test yes no).evalArithmetic x =
      if test.evalArithmetic x = 0 then yes.evalArithmetic x else no.evalArithmetic x := by
  rcases zero_or_succ (test.evalArithmetic x) with (h | ⟨n, h⟩)
  · simp [ifZero, h]
  · simp [ifZero, h, evalArithmetic_prec_succ]

@[simp] theorem evalArithmetic_nonzeroTest (x : M) :
    nonzeroTest.evalArithmetic x = if x = 0 then 0 else 1 := by
  by_cases h : x = 0 <;> simp [nonzeroTest, h]

@[simp] theorem evalArithmetic_boundedAll_zero (test : PrimitiveProgram) (z : M) :
    (boundedAll test).evalArithmetic (Arithmetic.pair z 0) = 1 := by
  simp [boundedAll]

theorem evalArithmetic_boundedAll_succ (test : PrimitiveProgram) (z n : M) :
    (boundedAll test).evalArithmetic (Arithmetic.pair z (n + 1)) =
      (boundedAll test).evalArithmetic (Arithmetic.pair z n) *
        (if test.evalArithmetic (Arithmetic.pair z n) = 0 then 0 else 1) := by
  rw [boundedAll, evalArithmetic_prec_succ]
  simp

open Classical in
theorem evalArithmetic_boundedAll (test : PrimitiveProgram) (z n : M) :
    (boundedAll test).evalArithmetic (Arithmetic.pair z n) =
      if ∀ i < n, test.evalArithmetic (Arithmetic.pair z i) ≠ 0 then 1 else 0 := by
  induction n using ISigma1.sigma1_succ_induction
  · let B : M → Prop := fun n ↦ ∀ i < n, test.evalArithmetic (Arithmetic.pair z i) ≠ 0
    have hB : 𝚫₁-Predicate B := by
      dsimp [B]
      definability
    apply HierarchySymbol.Definable.of_iff
      (Q := fun v : Fin 1 → M ↦
        (B (v 0) ∧ (boundedAll test).evalArithmetic (Arithmetic.pair z (v 0)) = 1) ∨
        (¬ B (v 0) ∧ (boundedAll test).evalArithmetic (Arithmetic.pair z (v 0)) = 0))
    · definability
    · intro v
      change (_ = if B (v 0) then 1 else 0) ↔ _
      by_cases h : B (v 0) <;> simp [h]
  case zero => simp
  case succ n ih =>
    rw [evalArithmetic_boundedAll_succ, ih]
    have h : (∀ i < n + 1, test.evalArithmetic (Arithmetic.pair z i) ≠ 0) ↔
        (∀ i < n, test.evalArithmetic (Arithmetic.pair z i) ≠ 0) ∧
          test.evalArithmetic (Arithmetic.pair z n) ≠ 0 := by
      constructor
      · intro h
        exact ⟨fun i hi ↦ h i (lt_trans hi (by simp)), h n (by simp)⟩
      · rintro ⟨h, hn⟩ i hi
        rcases (lt_succ_iff_le.mp hi).lt_or_eq with hi | rfl
        · exact h i hi
        · exact hn
    by_cases hall : ∀ i < n, test.evalArithmetic (Arithmetic.pair z i) ≠ 0
    <;> by_cases hn : test.evalArithmetic (Arithmetic.pair z n) = 0
    <;> simp [h, hall, hn]

@[simp] theorem evalArithmetic_boundedAll_eq_one (test : PrimitiveProgram) (z n : M) :
    (boundedAll test).evalArithmetic (Arithmetic.pair z n) = 1 ↔
      ∀ i < n, test.evalArithmetic (Arithmetic.pair z i) ≠ 0 := by
  classical
  rw [evalArithmetic_boundedAll]
  split_ifs <;> simp_all

def boundedExists (test : PrimitiveProgram) : PrimitiveProgram :=
  .comp zeroTest (boundedAll (.comp zeroTest test))

@[simp] theorem evalArithmetic_boundedExists_eq_one (test : PrimitiveProgram) (z n : M) :
    (boundedExists test).evalArithmetic (Arithmetic.pair z n) = 1 ↔
      ∃ i < n, test.evalArithmetic (Arithmetic.pair z i) ≠ 0 := by
  classical
  simp [boundedExists, evalArithmetic_boundedAll, not_forall]
end PrimitiveProgram
end ZFVP
