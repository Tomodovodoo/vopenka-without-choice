import ZFVP.Syntax.PrimitiveProgramNegation

/-! Explicit term and argument rewriting for the eigenvariable and witness rules. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def ifLess (a b yes no : PrimitiveProgram) : PrimitiveProgram :=
  ifZero (.comp lessEqual (.pair b a)) yes no

def proofRewriteTerm : PrimitiveProgram :=
  let s := .left
  let d := .comp .left .right
  let c := .comp .right .right
  let t := .comp listHead c
  let i := .comp listTail c
  let bound := tagged 0 i
  let fresh := tagged 1 (ifEqual s (constant 1) .zero (.comp subtraction (.pair s (constant 2))))
  ifEqual t (constant 0)
    (ifZero s bound (ifLess i d bound (ifEqual i d fresh (tagged 0 (.comp predecessor i)))))
    (tagged 1 (ifLess s (constant 2) (.comp .succ i) i))

def vectorTwo (a b : PrimitiveProgram) : PrimitiveProgram :=
  .comp .succ (.pair a (.comp .succ (.pair b .zero)))

def proofRewriteArguments : PrimitiveProgram :=
  let s := .left
  let d := .comp .left .right
  let c := .comp .right .right
  vectorTwo
    (.comp proofRewriteTerm (.pair s (.pair d (.comp listHead c))))
    (.comp proofRewriteTerm (.pair s (.pair d (.comp listHead (.comp listTail c)))))

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem evalArithmetic_ifLess (a b yes no : PrimitiveProgram) (x : M) :
    (ifLess a b yes no).evalArithmetic x =
      if a.evalArithmetic x < b.evalArithmetic x then yes.evalArithmetic x else no.evalArithmetic x := by
  by_cases h : a.evalArithmetic x < b.evalArithmetic x
  · have hn : ¬ b.evalArithmetic x ≤ a.evalArithmetic x := not_le.mpr h
    simp [ifLess, h, hn]
  · have hn : b.evalArithmetic x ≤ a.evalArithmetic x := le_of_not_gt h
    simp [ifLess, h, hn]

noncomputable def arithmeticProofRewriteTerm (s d c : M) : M :=
  let t := Arithmetic.pi₁ (c - 1)
  let i := Arithmetic.pi₂ (c - 1)
  if t = 0 then
    if s = 0 ∨ i < d then Arithmetic.pair 0 i + 1
    else if i = d then Arithmetic.pair 1 (if s = 1 then 0 else s - 2) + 1
    else Arithmetic.pair 0 (i - 1) + 1
  else Arithmetic.pair 1 (if s < 2 then i + 1 else i) + 1

@[simp] theorem evalArithmetic_proofRewriteTerm (s d c : M) :
    proofRewriteTerm.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d c)) =
      arithmeticProofRewriteTerm s d c := by
  by_cases hs : s = 0 <;> by_cases hi : Arithmetic.pi₂ (c - 1) < d <;>
    simp [proofRewriteTerm, arithmeticProofRewriteTerm, hs, hi]

@[simp] theorem evalArithmetic_vectorTwo (a b : PrimitiveProgram) (x : M) :
    (vectorTwo a b).evalArithmetic x =
      Arithmetic.pair (a.evalArithmetic x) (Arithmetic.pair (b.evalArithmetic x) 0 + 1) + 1 := by
  simp [vectorTwo]

@[simp] theorem evalArithmetic_proofRewriteArguments (s d c : M) :
    proofRewriteArguments.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d c)) =
      Arithmetic.pair (arithmeticProofRewriteTerm s d (listHead.evalArithmetic c))
        (Arithmetic.pair (arithmeticProofRewriteTerm s d (listHead.evalArithmetic (listTail.evalArithmetic c))) 0 + 1) + 1 := by
  simp [proofRewriteArguments]

end PrimitiveProgram
end ZFVP