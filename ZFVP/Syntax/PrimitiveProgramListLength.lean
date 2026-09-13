import ZFVP.Syntax.PrimitiveProgramLists

/-! The length of every internal successor-pair list code. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def listLengthRun : PrimitiveProgram :=
  .prec .zero (ifZero (.comp listDrop (.pair .left (.comp .left .right)))
    (.comp .right .right) (.comp .succ (.comp .right .right)))

def listLength : PrimitiveProgram := .comp listLengthRun (.pair identity identity)

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem evalArithmetic_listLengthRun_zero (xs : M) :
    listLengthRun.evalArithmetic (Arithmetic.pair xs 0) = 0 := by simp [listLengthRun]

theorem evalArithmetic_listLengthRun_succ (xs n : M) :
    listLengthRun.evalArithmetic (Arithmetic.pair xs (n + 1)) =
      if listDrop.evalArithmetic (Arithmetic.pair xs n) = 0 then
        listLengthRun.evalArithmetic (Arithmetic.pair xs n)
      else listLengthRun.evalArithmetic (Arithmetic.pair xs n) + 1 := by
  rw [listLengthRun, evalArithmetic_prec_succ]
  simp

theorem listDrop_has_length (xs : M) :
    ∃ m ≤ xs, ∀ n, listDrop.evalArithmetic (Arithmetic.pair xs n) ≠ 0 ↔ n < m := by
  have hP : 𝚺₁-Predicate (fun n : M ↦ listDrop.evalArithmetic (Arithmetic.pair xs n) = 0) := by
    definability
  obtain ⟨m, hm, hmin⟩ := InductionOnHierarchy.least_number_sigma 𝚺 1 hP
    (evalArithmetic_listDrop_exhausted xs xs le_rfl)
  have hmx : m ≤ xs := by
    by_contra h
    exact hmin xs (lt_of_not_ge h) (evalArithmetic_listDrop_exhausted xs xs le_rfl)
  refine ⟨m, hmx, fun n ↦ ⟨?_, fun hn ↦ hmin n hn⟩⟩
  intro hn
  by_contra h
  exact hn (evalArithmetic_listDrop_zero_mono hm (le_of_not_gt h))

theorem evalArithmetic_listLengthRun_min (xs m : M)
    (hm : ∀ n, listDrop.evalArithmetic (Arithmetic.pair xs n) ≠ 0 ↔ n < m) (n : M) :
    listLengthRun.evalArithmetic (Arithmetic.pair xs n) = min n m := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    rw [evalArithmetic_listLengthRun_succ, ih]
    by_cases hn : n < m
    · have hd := (hm n).mpr hn
      simp [hd, min_eq_left (le_of_lt hn), min_eq_left (lt_iff_succ_le.mp hn)]
    · have hd : listDrop.evalArithmetic (Arithmetic.pair xs n) = 0 := by
        exact not_not.mp (fun h ↦ hn ((hm n).mp h))
      have hmn := le_of_not_gt hn
      have hmn' : m ≤ n + 1 := hmn.trans le_self_add
      simp [hd, min_eq_right hmn, min_eq_right hmn']

theorem evalArithmetic_listLength_spec (xs : M) :
    listLength.evalArithmetic xs ≤ xs ∧
      ∀ n, listDrop.evalArithmetic (Arithmetic.pair xs n) ≠ 0 ↔ n < listLength.evalArithmetic xs := by
  obtain ⟨m, hmx, hm⟩ := listDrop_has_length xs
  have he : listLength.evalArithmetic xs = m := by
    simp [listLength, evalArithmetic_listLengthRun_min xs m hm, min_eq_right hmx]
  simpa [he] using And.intro hmx hm

@[simp] theorem evalArithmetic_listDrop_ne_zero (xs n : M) :
    listDrop.evalArithmetic (Arithmetic.pair xs n) ≠ 0 ↔ n < listLength.evalArithmetic xs :=
  (evalArithmetic_listLength_spec xs).2 n

@[simp] theorem evalArithmetic_listDrop_eq_zero (xs n : M) :
    listDrop.evalArithmetic (Arithmetic.pair xs n) = 0 ↔ listLength.evalArithmetic xs ≤ n := by
  simpa only [not_not, not_lt] using not_congr (evalArithmetic_listDrop_ne_zero xs n)

theorem evalArithmetic_listLength_le (xs : M) : listLength.evalArithmetic xs ≤ xs :=
  (evalArithmetic_listLength_spec xs).1

@[simp] theorem evalArithmetic_listLength_zero : listLength.evalArithmetic (0 : M) = 0 :=
  le_antisymm (evalArithmetic_listLength_le 0) (Arithmetic.zero_le _)

@[simp] theorem evalArithmetic_listLength_cons (x xs : M) :
    listLength.evalArithmetic (Arithmetic.pair x xs + 1) = listLength.evalArithmetic xs + 1 := by
  apply le_antisymm
  · apply (evalArithmetic_listDrop_eq_zero _ _).mp
    rw [evalArithmetic_listDrop_cons]
    exact (evalArithmetic_listDrop_eq_zero _ _).mpr le_rfl
  · apply lt_iff_succ_le.mp
    apply (evalArithmetic_listDrop_ne_zero _ _).mp
    rcases zero_or_succ (listLength.evalArithmetic xs) with h | ⟨n, h⟩
    · rw [h, evalArithmetic_listDrop_zero]
      simp
    · rw [h, evalArithmetic_listDrop_cons, evalArithmetic_listDrop_ne_zero, h]
      simp

@[simp] theorem evalArithmetic_listLength_encode (xs : List ℕ) :
    listLength.evalArithmetic (Encodable.encode xs) = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [Encodable.encode_list_cons, ← arithmeticPair_nat]
    simpa using ih

end PrimitiveProgram
end ZFVP
