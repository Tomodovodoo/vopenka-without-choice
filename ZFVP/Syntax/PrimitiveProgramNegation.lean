import ZFVP.Syntax.PrimitiveProgramCourseRec

/-! An explicit program for negating natural-number formula codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def tagged (tag : ℕ) (payload : PrimitiveProgram) : PrimitiveProgram :=
  .comp .succ (.pair (constant tag) payload)

def ifEqual (a b yes no : PrimitiveProgram) : PrimitiveProgram :=
  ifZero (.comp equal (.pair a b)) no yes

def negateStep : PrimitiveProgram :=
  let n := .comp .left .right
  let t := .comp listHead n
  let c := .comp listTail n
  let table := .comp .right .right
  let prev := fun i ↦ .comp listGet (.pair table (.comp subtraction (.pair n (.comp .succ i))))
  let bin := .pair (prev (.comp .left c)) (prev (.comp .right c))
  ifZero n .zero
    (ifEqual t (constant 0) (tagged 1 c)
    (ifEqual t (constant 1) (tagged 0 c)
    (ifEqual t (constant 2) (tagged 3 .zero)
    (ifEqual t (constant 3) (tagged 2 .zero)
    (ifEqual t (constant 4) (tagged 5 bin)
    (ifEqual t (constant 5) (tagged 4 bin)
    (ifEqual t (constant 6) (tagged 7 (prev c))
    (ifEqual t (constant 7) (tagged 6 (prev c)) .zero))))))))

def negateCode : PrimitiveProgram := .comp (courseEval negateStep) (.pair .zero identity)

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem evalArithmetic_tagged (tag : ℕ) (payload : PrimitiveProgram) (x : M) :
    (tagged tag payload).evalArithmetic x = Arithmetic.pair (tag : M) (payload.evalArithmetic x) + 1 := by
  simp [tagged]

@[simp] theorem evalArithmetic_ifEqual (a b yes no : PrimitiveProgram) (x : M) :
    (ifEqual a b yes no).evalArithmetic x =
      if a.evalArithmetic x = b.evalArithmetic x then yes.evalArithmetic x else no.evalArithmetic x := by
  by_cases h : a.evalArithmetic x = b.evalArithmetic x <;> simp [ifEqual, h]

noncomputable def negateArithmeticStep (n table : M) : M :=
  let t := Arithmetic.pi₁ (n - 1)
  let c := Arithmetic.pi₂ (n - 1)
  let prev := fun i ↦ listGet.evalArithmetic (Arithmetic.pair table (n - (i + 1)))
  if n = 0 then 0
  else if t = 0 then Arithmetic.pair 1 c + 1
  else if t = 1 then Arithmetic.pair 0 c + 1
  else if t = 2 then Arithmetic.pair 3 0 + 1
  else if t = 3 then Arithmetic.pair 2 0 + 1
  else if t = 4 then Arithmetic.pair 5 (Arithmetic.pair (prev (Arithmetic.pi₁ c)) (prev (Arithmetic.pi₂ c))) + 1
  else if t = 5 then Arithmetic.pair 4 (Arithmetic.pair (prev (Arithmetic.pi₁ c)) (prev (Arithmetic.pi₂ c))) + 1
  else if t = 6 then Arithmetic.pair 7 (prev c) + 1
  else if t = 7 then Arithmetic.pair 6 (prev c) + 1
  else 0

@[simp] theorem evalArithmetic_negateStep (z n table : M) :
    negateStep.evalArithmetic (Arithmetic.pair z (Arithmetic.pair n table)) = negateArithmeticStep n table := by
  simp [negateStep, negateArithmeticStep]

theorem evalArithmetic_negateCode (n : M) :
    negateCode.evalArithmetic n =
      negateArithmeticStep n ((courseTable negateStep).evalArithmetic (Arithmetic.pair 0 n)) := by
  simp [negateCode, evalArithmetic_courseEval]

theorem evalArithmetic_negateCode_prev (n i : M) (hi : i < n) :
    listGet.evalArithmetic (Arithmetic.pair ((courseTable negateStep).evalArithmetic (Arithmetic.pair 0 n))
      (n - (i + 1))) = negateCode.evalArithmetic i := by
  rw [evalArithmetic_courseTable_get negateStep 0 n i hi]
  simp [negateCode]

@[simp] theorem evalArithmetic_negateCode_zero : negateCode.evalArithmetic (0 : M) = 0 := by
  simp [evalArithmetic_negateCode, negateArithmeticStep]

@[simp] theorem evalArithmetic_negateCode_rel (c : M) :
    negateCode.evalArithmetic (Arithmetic.pair 0 c + 1) = Arithmetic.pair 1 c + 1 := by
  rw [evalArithmetic_negateCode]
  simp [negateArithmeticStep]

@[simp] theorem evalArithmetic_negateCode_nrel (c : M) :
    negateCode.evalArithmetic (Arithmetic.pair 1 c + 1) = Arithmetic.pair 0 c + 1 := by
  rw [evalArithmetic_negateCode]
  simp [negateArithmeticStep]

@[simp] theorem evalArithmetic_negateCode_verum (c : M) :
    negateCode.evalArithmetic (Arithmetic.pair 2 c + 1) = Arithmetic.pair 3 0 + 1 := by
  rw [evalArithmetic_negateCode]
  simp [negateArithmeticStep]

@[simp] theorem evalArithmetic_negateCode_falsum (c : M) :
    negateCode.evalArithmetic (Arithmetic.pair 3 c + 1) = Arithmetic.pair 2 0 + 1 := by
  rw [evalArithmetic_negateCode]
  simp [negateArithmeticStep]

theorem binaryCode_left_lt (t a b : M) : a < Arithmetic.pair t (Arithmetic.pair a b) + 1 :=
  lt_succ_iff_le.mpr ((le_pair_left a b).trans (le_pair_right t _))

theorem binaryCode_right_lt (t a b : M) : b < Arithmetic.pair t (Arithmetic.pair a b) + 1 :=
  lt_succ_iff_le.mpr ((le_pair_right a b).trans (le_pair_right t _))

@[simp] theorem evalArithmetic_negateCode_and (a b : M) :
    negateCode.evalArithmetic (Arithmetic.pair 4 (Arithmetic.pair a b) + 1) =
      Arithmetic.pair 5 (Arithmetic.pair (negateCode.evalArithmetic a) (negateCode.evalArithmetic b)) + 1 := by
  rw [evalArithmetic_negateCode]
  simp [negateArithmeticStep, evalArithmetic_negateCode_prev _ a (binaryCode_left_lt 4 a b),
    evalArithmetic_negateCode_prev _ b (binaryCode_right_lt 4 a b)]

@[simp] theorem evalArithmetic_negateCode_or (a b : M) :
    negateCode.evalArithmetic (Arithmetic.pair 5 (Arithmetic.pair a b) + 1) =
      Arithmetic.pair 4 (Arithmetic.pair (negateCode.evalArithmetic a) (negateCode.evalArithmetic b)) + 1 := by
  rw [evalArithmetic_negateCode]
  simp [negateArithmeticStep, evalArithmetic_negateCode_prev _ a (binaryCode_left_lt 5 a b),
    evalArithmetic_negateCode_prev _ b (binaryCode_right_lt 5 a b)]

@[simp] theorem evalArithmetic_negateCode_all (a : M) :
    negateCode.evalArithmetic (Arithmetic.pair 6 a + 1) =
      Arithmetic.pair 7 (negateCode.evalArithmetic a) + 1 := by
  rw [evalArithmetic_negateCode]
  simp [negateArithmeticStep, evalArithmetic_negateCode_prev _ a (lt_succ_iff_le.mpr (le_pair_right 6 a))]

@[simp] theorem evalArithmetic_negateCode_exs (a : M) :
    negateCode.evalArithmetic (Arithmetic.pair 7 a + 1) =
      Arithmetic.pair 6 (negateCode.evalArithmetic a) + 1 := by
  rw [evalArithmetic_negateCode]
  simp [negateArithmeticStep, evalArithmetic_negateCode_prev _ a (lt_succ_iff_le.mpr (le_pair_right 7 a))]

end PrimitiveProgram
end ZFVP
