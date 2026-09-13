import ZFVP.ModelTheory.InternalProgramListExt
import ZFVP.Syntax.PrimitiveProgramListMembership

/-! Arithmetic list tests coincide with membership and inclusion of decoded sequence ranges. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem mem_range_decodedNaturalList (xs x : V) :
    x ∈ SetTheory.range (decodedNaturalList xs) ↔
      ∃ i ∈ listLength.evalSet xs, x = listGet.evalSet (naturalSquarePair xs i) := by
  simp only [SetTheory.mem_range_iff, decodedNaturalList, pair_mem_definableGraph_iff]

theorem mem_range_decodedNaturalList_val (x xs : InternalArithmetic V) :
    internalArithmeticVal x ∈ SetTheory.range (decodedNaturalList (internalArithmeticVal xs)) ↔
      ∃ i < listLength.evalArithmetic xs, x = listGet.evalArithmetic (Arithmetic.pair xs i) := by
  rw [mem_range_decodedNaturalList]
  constructor
  · rintro ⟨i, hi, he⟩
    have hiω : i ∈ (ω : V) := IsTransitive.transitive _
      (evalSet_natural listLength (internalArithmeticVal_mem xs)) _ hi
    obtain ⟨j, rfl⟩ := internalArithmeticVal_surjective hiω
    refine ⟨j, ?_, ?_⟩
    · rw [internalArithmetic_lt, evalArithmetic_agreement]
      exact hi
    · apply internalArithmeticVal_injective
      simpa only [evalSet_pair_val] using he
  · rintro ⟨i, hi, he⟩
    refine ⟨internalArithmeticVal i, ?_, ?_⟩
    · rw [← evalArithmetic_agreement, ← internalArithmetic_lt]
      exact hi
    · rw [evalSet_pair_val, he]

theorem evalSet_listMember_iff {x xs : V} (hx : x ∈ (ω : V)) (hxs : xs ∈ (ω : V)) :
    listMember.evalSet (naturalSquarePair x xs) = 1 ↔ x ∈ SetTheory.range (decodedNaturalList xs) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hx
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hxs
  rw [evalSet_pair_val, ← internalArithmeticVal_one, ← internalArithmetic_eq,
    evalArithmetic_listMember_eq_one, mem_range_decodedNaturalList_val]

theorem evalSet_listSubset_iff {xs ys : V} (hx : xs ∈ (ω : V)) (hy : ys ∈ (ω : V)) :
    listSubset.evalSet (naturalSquarePair xs ys) = 1 ↔
      SetTheory.range (decodedNaturalList xs) ⊆ SetTheory.range (decodedNaturalList ys) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hx
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hy
  rw [evalSet_pair_val, ← internalArithmeticVal_one, ← internalArithmetic_eq,
    evalArithmetic_listSubset_eq_one]
  constructor
  · intro h x hx
    have hxω : x ∈ (ω : V) := range_subset_of_mem_function
      (decodedNaturalList_mem_function (internalArithmeticVal_mem u)) _ hx
    obtain ⟨w, rfl⟩ := internalArithmeticVal_surjective hxω
    obtain ⟨i, hi, he⟩ := (mem_range_decodedNaturalList_val w u).mp hx
    obtain ⟨j, hj, hjv⟩ := h i hi
    exact (mem_range_decodedNaturalList_val w v).mpr ⟨j, hj, he.trans hjv⟩
  · intro h i hi
    have hm := (mem_range_decodedNaturalList_val
      (listGet.evalArithmetic (Arithmetic.pair u i)) u).mpr ⟨i, hi, rfl⟩
    exact (mem_range_decodedNaturalList_val _ v).mp (h _ hm)

end ZFVP
