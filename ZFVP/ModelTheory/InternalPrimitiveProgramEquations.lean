import ZFVP.ModelTheory.InternalPrimitiveProgram

/-! The program equations hold throughout internal omega, including at nonstandard inputs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

@[simp] theorem evalSet_zero (x : V) : PrimitiveProgram.zero.evalSet x = 0 := rfl
@[simp] theorem evalSet_succ (x : V) : PrimitiveProgram.succ.evalSet x = SetTheory.succ x := rfl
@[simp] theorem evalSet_left (x : V) : PrimitiveProgram.left.evalSet x = naturalSquareLeft x := rfl
@[simp] theorem evalSet_right (x : V) : PrimitiveProgram.right.evalSet x = naturalSquareRight x := rfl

@[simp] theorem evalSet_pair (a b : PrimitiveProgram) (x : V) :
    (PrimitiveProgram.pair a b).evalSet x = naturalSquarePair (a.evalSet x) (b.evalSet x) := rfl

@[simp] theorem evalSet_comp (a b : PrimitiveProgram) (x : V) :
    (PrimitiveProgram.comp a b).evalSet x = a.evalSet (b.evalSet x) := rfl

theorem evalSet_prec (a b : PrimitiveProgram) (x : V) :
    (PrimitiveProgram.prec a b).evalSet x = naturalPrec a.evalSet b.evalSet
      (evalSet_definable a) (evalSet_definable b) x := rfl

theorem evalSet_prec_pair (a b : PrimitiveProgram) {z n : V} (hz : z ∈ (ω : V)) (hn : n ∈ (ω : V)) :
    (PrimitiveProgram.prec a b).evalSet (naturalSquarePair z n) =
      naturalPrimitive a.evalSet b.evalSet (evalSet_definable a) (evalSet_definable b) z n := by
  simp only [evalSet_prec, naturalPrec, naturalSquareLeft, naturalSquareRight,
    naturalSquareUnpair_pair hz hn]

@[simp] theorem evalSet_prec_zero (a b : PrimitiveProgram) {z : V} (hz : z ∈ (ω : V)) :
    (PrimitiveProgram.prec a b).evalSet (naturalSquarePair z 0) = a.evalSet z := by
  rw [evalSet_prec_pair a b hz (by simp), naturalPrimitive_zero]

theorem evalSet_prec_succ (a b : PrimitiveProgram) {z n : V}
    (hz : z ∈ (ω : V)) (hn : n ∈ (ω : V)) :
    (PrimitiveProgram.prec a b).evalSet (naturalSquarePair z (SetTheory.succ n)) =
      b.evalSet (naturalSquarePair z (naturalSquarePair n
        ((PrimitiveProgram.prec a b).evalSet (naturalSquarePair z n)))) := by
  rw [evalSet_prec_pair a b hz (ω_succ_closed hn), naturalPrimitive_succ _ _ _ _ _ hn,
    evalSet_prec_pair a b hz hn]

end PrimitiveProgram
end ZFVP
