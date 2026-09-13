import ZFVP.Syntax.PrimitiveProgramBounded
import ZFVP.Syntax.ArithmeticPrimitiveProgramStandard

/-! Explicit operations on successor-pair list codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def listHead : PrimitiveProgram := .comp .left predecessor

def listTail : PrimitiveProgram := .comp .right predecessor

def listDrop : PrimitiveProgram := .prec identity (.comp listTail (.comp .right .right))

def listGet : PrimitiveProgram := .comp listHead listDrop

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem evalArithmetic_listHead (x : M) :
    listHead.evalArithmetic x = Arithmetic.pi₁ (x - 1) := by simp [listHead]

@[simp] theorem evalArithmetic_listTail (x : M) :
    listTail.evalArithmetic x = Arithmetic.pi₂ (x - 1) := by simp [listTail]

@[simp] theorem evalArithmetic_listHead_cons (x xs : M) :
    listHead.evalArithmetic (Arithmetic.pair x xs + 1) = x := by simp

@[simp] theorem evalArithmetic_listTail_cons (x xs : M) :
    listTail.evalArithmetic (Arithmetic.pair x xs + 1) = xs := by simp

@[simp] theorem evalArithmetic_listDrop_zero (xs : M) :
    listDrop.evalArithmetic (Arithmetic.pair xs 0) = xs := by simp [listDrop]

theorem evalArithmetic_listDrop_succ (xs n : M) :
    listDrop.evalArithmetic (Arithmetic.pair xs (n + 1)) =
      listTail.evalArithmetic (listDrop.evalArithmetic (Arithmetic.pair xs n)) := by
  rw [listDrop, evalArithmetic_prec_succ]
  simp

theorem evalArithmetic_listDrop_le (xs n : M) :
    listDrop.evalArithmetic (Arithmetic.pair xs n) ≤ xs - n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    rw [evalArithmetic_listDrop_succ, evalArithmetic_listTail]
    exact le_trans (Arithmetic.pi₂_le_self _) (by simpa [Arithmetic.sub_sub] using tsub_le_tsub_right ih 1)

@[simp] theorem evalArithmetic_listDrop_exhausted (xs n : M) (h : xs ≤ n) :
    listDrop.evalArithmetic (Arithmetic.pair xs n) = 0 := by
  apply le_antisymm _ (Arithmetic.zero_le _)
  simpa [sub_spec_of_le h] using evalArithmetic_listDrop_le xs n

@[simp] theorem evalArithmetic_listDrop_nil (n : M) :
    listDrop.evalArithmetic (Arithmetic.pair (0 : M) n) = 0 := by simp

@[simp] theorem evalArithmetic_listGet (xs n : M) :
    listGet.evalArithmetic (Arithmetic.pair xs n) =
      listHead.evalArithmetic (listDrop.evalArithmetic (Arithmetic.pair xs n)) := rfl

@[simp] theorem evalArithmetic_listTail_zero : listTail.evalArithmetic (0 : M) = 0 := by
  simp only [evalArithmetic_listTail, Arithmetic.zero_sub]
  exact le_antisymm (Arithmetic.pi₂_le_self 0) (Arithmetic.zero_le _)

@[simp] theorem evalArithmetic_listHead_zero : listHead.evalArithmetic (0 : M) = 0 := by
  simp only [evalArithmetic_listHead, Arithmetic.zero_sub]
  exact le_antisymm (Arithmetic.pi₁_le_self 0) (Arithmetic.zero_le _)

theorem evalArithmetic_listDrop_add (xs n k : M) :
    listDrop.evalArithmetic (Arithmetic.pair xs (n + k)) =
      listDrop.evalArithmetic (Arithmetic.pair (listDrop.evalArithmetic (Arithmetic.pair xs n)) k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    rw [← add_assoc, evalArithmetic_listDrop_succ, evalArithmetic_listDrop_succ, ih]

@[simp] theorem evalArithmetic_listDrop_cons (x xs n : M) :
    listDrop.evalArithmetic (Arithmetic.pair (Arithmetic.pair x xs + 1) (n + 1)) =
      listDrop.evalArithmetic (Arithmetic.pair xs n) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    rw [evalArithmetic_listDrop_succ]
    simp
  case succ n ih => rw [evalArithmetic_listDrop_succ, ih, evalArithmetic_listDrop_succ]

theorem evalArithmetic_listDrop_zero_mono {xs n k : M}
    (h : listDrop.evalArithmetic (Arithmetic.pair xs n) = 0) (hnk : n ≤ k) :
    listDrop.evalArithmetic (Arithmetic.pair xs k) = 0 := by
  obtain ⟨l, rfl⟩ := le_iff_exists_add.mp hnk
  rw [evalArithmetic_listDrop_add, h, evalArithmetic_listDrop_nil]

@[simp] theorem evalArithmetic_listDrop_encode (xs : List ℕ) (n : ℕ) :
    listDrop.evalArithmetic (Arithmetic.pair (Encodable.encode xs) n) =
      Encodable.encode (xs.drop n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [evalArithmetic_listDrop_succ, ih]
    cases h : xs.drop n with
    | nil => simp [List.drop_add_one_eq_tail_drop, h, Arithmetic.pi₂, arithmeticUnpair_nat]
    | cons y ys => simp [h, List.drop_add_one_eq_tail_drop, Encodable.encode_list_cons, ← arithmeticPair_nat]

@[simp] theorem evalArithmetic_listGet_cons_zero (x xs : M) :
    listGet.evalArithmetic (Arithmetic.pair (Arithmetic.pair x xs + 1) 0) = x := by simp

@[simp] theorem evalArithmetic_listGet_cons_succ (x xs n : M) :
    listGet.evalArithmetic (Arithmetic.pair (Arithmetic.pair x xs + 1) (n + 1)) =
      listGet.evalArithmetic (Arithmetic.pair xs n) := by simp

@[simp] theorem evalArithmetic_listGet_encode (xs : List ℕ) (n : ℕ) (hn : n < xs.length) :
    listGet.evalArithmetic (Arithmetic.pair (Encodable.encode xs) n) = xs[n] := by
  induction xs generalizing n with
  | nil => simp at hn
  | cons x xs ih =>
    rw [Encodable.encode_list_cons, ← arithmeticPair_nat]
    cases n with
    | zero => simp
    | succ n =>
      simp only [Nat.succ_eq_add_one]
      rw [evalArithmetic_listGet_cons_succ]
      exact ih n (by simpa using hn)

end PrimitiveProgram
end ZFVP
