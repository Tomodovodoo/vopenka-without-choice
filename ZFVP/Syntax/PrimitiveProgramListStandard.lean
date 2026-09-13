import ZFVP.Syntax.PrimitiveProgramListMemberEquations
import ZFVP.Syntax.PrimitiveProgramLKCertificate
import ZFVP.Syntax.PrimitiveProgramProofRewriteStandard

/-! Exact behavior of the list programs on standard encoded lists. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

theorem encode_list_map_encode {α : Type*} [Encodable α] (xs : List α) :
    Encodable.encode (xs.map Encodable.encode) = Encodable.encode xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, Encodable.encode_list_cons, Encodable.encode_nat, ih]

namespace PrimitiveProgram

theorem listMember_encode_nat (x : ℕ) (xs : List ℕ) :
    listMember.eval (Nat.pair x (Encodable.encode xs)) = 1 ↔ x ∈ xs := by
  rw [← evalArithmetic_nat, ← arithmeticPair_nat, evalArithmetic_listMember_eq_one,
    evalArithmetic_listLength_encode]
  constructor
  · rintro ⟨i, hi, he⟩
    rw [evalArithmetic_listGet_encode xs i hi] at he
    exact List.mem_iff_getElem.mpr ⟨i, hi, he.symm⟩
  · intro hx
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
    exact ⟨i, hi, by rw [evalArithmetic_listGet_encode xs i hi, he]⟩

theorem listMember_encode {α : Type*} [Encodable α] (x : α) (xs : List α) :
    listMember.eval (Nat.pair (Encodable.encode x) (Encodable.encode xs)) = 1 ↔ x ∈ xs := by
  rw [← encode_list_map_encode xs, listMember_encode_nat]
  simp

theorem listSubset_encode_nat (xs ys : List ℕ) :
    listSubset.eval (Nat.pair (Encodable.encode xs) (Encodable.encode ys)) = 1 ↔ xs ⊆ ys := by
  rw [← evalArithmetic_nat, ← arithmeticPair_nat, evalArithmetic_listSubset_eq_one,
    evalArithmetic_listLength_encode, evalArithmetic_listLength_encode]
  constructor
  · intro h x hx
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
    obtain ⟨j, hj, heq⟩ := h i hi
    rw [evalArithmetic_listGet_encode xs i hi, evalArithmetic_listGet_encode ys j hj, he] at heq
    exact List.mem_iff_getElem.mpr ⟨j, hj, heq.symm⟩
  · intro h i hi
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp (h (List.getElem_mem hi))
    exact ⟨j, hj, by rw [evalArithmetic_listGet_encode xs i hi, evalArithmetic_listGet_encode ys j hj, he]⟩

theorem listSubset_encode {α : Type*} [Encodable α] (xs ys : List α) :
    listSubset.eval (Nat.pair (Encodable.encode xs) (Encodable.encode ys)) = 1 ↔ xs ⊆ ys := by
  rw [← encode_list_map_encode xs, ← encode_list_map_encode ys, listSubset_encode_nat]
  constructor
  · intro h x hx
    have hm := h (List.mem_map.mpr ⟨x, hx, rfl⟩)
    simpa using hm
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact List.mem_map.mpr ⟨y, h hy, rfl⟩

theorem listAppend_encode {α : Type*} [Encodable α] (xs ys : List α) :
    listAppend.eval (Nat.pair (Encodable.encode ys) (Encodable.encode xs)) = Encodable.encode (xs ++ ys) := by
  induction xs with
  | nil =>
    rw [← evalArithmetic_nat, ← arithmeticPair_nat]
    exact evalArithmetic_listAppend_zero _
  | cons x xs ih =>
    have h := evalArithmetic_listAppend_cons (Encodable.encode ys : ℕ) (Encodable.encode x : ℕ) (Encodable.encode xs : ℕ)
    simp only [arithmeticPair_nat, evalArithmetic_nat] at h
    simp only [List.cons_append, Encodable.encode_list_cons, Nat.succ_eq_add_one]
    rw [h, ih]

theorem listMap_encode {α β : Type*} [Encodable α] [Encodable β] (f : PrimitiveProgram) (g : α → β)
    (z : ℕ) (hf : ∀ x, f.eval (Nat.pair z (Encodable.encode x)) = Encodable.encode (g x)) (xs : List α) :
    (listMap f).eval (Nat.pair z (Encodable.encode xs)) = Encodable.encode (xs.map g) := by
  induction xs with
  | nil =>
    rw [← evalArithmetic_nat, ← arithmeticPair_nat]
    exact evalArithmetic_listMap_zero f z
  | cons x xs ih =>
    have h := evalArithmetic_listMap_cons f (z : ℕ) (Encodable.encode x : ℕ) (Encodable.encode xs : ℕ)
    simp only [arithmeticPair_nat, evalArithmetic_nat] at h
    simp only [List.map_cons, Encodable.encode_list_cons, Nat.succ_eq_add_one]
    rw [h, hf, ih]

theorem listAll_encode_iff {α : Type*} [Encodable α] (f : PrimitiveProgram) (z : ℕ) (xs : List α) :
    (listAll f).eval (Nat.pair z (Encodable.encode xs)) = 1 ↔
      ∀ x ∈ xs, f.eval (Nat.pair z (Encodable.encode x)) ≠ 0 := by
  rw [← encode_list_map_encode xs, ← evalArithmetic_nat, ← arithmeticPair_nat,
    evalArithmetic_listAll_eq_one, evalArithmetic_listLength_encode]
  constructor
  · intro h x hx
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp (List.mem_map.mpr ⟨x, hx, rfl⟩ : Encodable.encode x ∈ xs.map Encodable.encode)
    have hv := h i hi
    rw [evalArithmetic_listGet_encode _ i hi, he, arithmeticPair_nat, evalArithmetic_nat] at hv
    exact hv
  · intro h i hi
    have hmem := List.getElem_mem hi
    obtain ⟨x, hx, he⟩ := List.mem_map.mp hmem
    rw [evalArithmetic_listGet_encode _ i hi, ← he, arithmeticPair_nat, evalArithmetic_nat]
    exact h x hx

end PrimitiveProgram
end ZFVP
