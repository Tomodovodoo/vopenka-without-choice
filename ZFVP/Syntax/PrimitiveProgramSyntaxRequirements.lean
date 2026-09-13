import ZFVP.Syntax.PrimitiveProgramNegation

/-! Explicit validity and bound-variable requirements for natural atomic syntax.
A zero result rejects the code. A positive result is one plus the number of
bound variables required. The Boolean parameter controls acceptance of free variables. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def maximum : PrimitiveProgram := ifZero lessEqual .left .right

def joinRequirements : PrimitiveProgram :=
  ifZero .left .zero (ifZero .right .zero maximum)

def termRequirement (allowFree : Bool) : PrimitiveProgram :=
  ifZero identity .zero
    (ifEqual listHead (constant 0) (.comp .succ (.comp .succ listTail))
      (ifEqual listHead (constant 1) (if allowFree then constant 1 else .zero) .zero))

def atomicRequirement (allowFree : Bool) : PrimitiveProgram :=
  let r := .comp .left .right
  let args := .comp .right .right
  let a := .comp (termRequirement allowFree) (.comp listHead args)
  let b := .comp (termRequirement allowFree) (.comp listHead (.comp listTail args))
  ifEqual .left (constant 2)
    (ifZero (.comp lessEqual (.pair r (constant 1))) .zero
      (ifEqual (.comp listLength args) (constant 2) (.comp joinRequirements (.pair a b)) .zero)) .zero

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem evalArithmetic_maximum (x y : M) :
    maximum.evalArithmetic (Arithmetic.pair x y) = max x y := by
  by_cases h : x ≤ y <;> simp [maximum, h, max_def]

@[simp] theorem evalArithmetic_joinRequirements (x y : M) :
    joinRequirements.evalArithmetic (Arithmetic.pair x y) =
      if x = 0 then 0 else if y = 0 then 0 else max x y := by
  simp [joinRequirements]

@[simp] theorem evalArithmetic_termRequirement (allowFree : Bool) (c : M) :
    (termRequirement allowFree).evalArithmetic c =
      if c = 0 then 0 else if Arithmetic.pi₁ (c - 1) = 0 then Arithmetic.pi₂ (c - 1) + 1 + 1
      else if Arithmetic.pi₁ (c - 1) = 1 then (if allowFree then 1 else 0) else 0 := by
  cases allowFree <;> simp [termRequirement]

@[simp] theorem evalArithmetic_termRequirement_bound (allowFree : Bool) (i : M) :
    (termRequirement allowFree).evalArithmetic (Arithmetic.pair 0 i + 1) = i + 1 + 1 := by
  simp

@[simp] theorem evalArithmetic_termRequirement_free (allowFree : Bool) (i : M) :
    (termRequirement allowFree).evalArithmetic (Arithmetic.pair 1 i + 1) = if allowFree then 1 else 0 := by
  simp

theorem evalArithmetic_atomicRequirement (allowFree : Bool) (k r args : M) :
    (atomicRequirement allowFree).evalArithmetic (Arithmetic.pair k (Arithmetic.pair r args)) =
      if k = 2 then if r ≤ 1 then if listLength.evalArithmetic args = 2 then
        joinRequirements.evalArithmetic (Arithmetic.pair
          ((termRequirement allowFree).evalArithmetic (listHead.evalArithmetic args))
          ((termRequirement allowFree).evalArithmetic (listHead.evalArithmetic (listTail.evalArithmetic args))))
      else 0 else 0 else 0 := by
  by_cases hr : r ≤ 1 <;> simp [atomicRequirement, hr]

end PrimitiveProgram
end ZFVP