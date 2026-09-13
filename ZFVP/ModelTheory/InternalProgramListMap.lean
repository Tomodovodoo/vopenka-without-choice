import ZFVP.ModelTheory.InternalProgramListMembership
import ZFVP.Syntax.PrimitiveProgramListMap

/-! Internal set semantics of explicit natural-number list maps and concatenation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem evalSet_listMap_zero (f : PrimitiveProgram) {z : V} (hz : z ∈ (ω : V)) :
    (listMap f).evalSet (naturalSquarePair z 0) = 0 := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hz
  have h := congrArg internalArithmeticVal (evalArithmetic_listMap_zero f u)
  simpa only [evalArithmetic_agreement, internalArithmeticVal_pair, internalArithmeticVal_zero] using h

theorem evalSet_listMap_cons (f : PrimitiveProgram) {z x xs : V}
    (hz : z ∈ (ω : V)) (hx : x ∈ (ω : V)) (hxs : xs ∈ (ω : V)) :
    (listMap f).evalSet (naturalSquarePair z (SetTheory.succ (naturalSquarePair x xs))) =
      SetTheory.succ (naturalSquarePair (f.evalSet (naturalSquarePair z x)) ((listMap f).evalSet (naturalSquarePair z xs))) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hz
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hx
  obtain ⟨w, rfl⟩ := internalArithmeticVal_surjective hxs
  have h := congrArg internalArithmeticVal (evalArithmetic_listMap_cons f u v w)
  simpa only [evalArithmetic_agreement, internalArithmeticVal_pair, internalArithmeticVal_succ] using h

theorem evalSet_listMap_length (f : PrimitiveProgram) {z xs : V} (hz : z ∈ (ω : V)) (hxs : xs ∈ (ω : V)) :
    listLength.evalSet ((listMap f).evalSet (naturalSquarePair z xs)) = listLength.evalSet xs := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hz
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hxs
  have h := congrArg internalArithmeticVal (evalArithmetic_listMap_length f u v)
  simpa only [evalArithmetic_agreement, internalArithmeticVal_pair] using h

theorem evalSet_listMap_get (f : PrimitiveProgram) {z xs i : V}
    (hz : z ∈ (ω : V)) (hxs : xs ∈ (ω : V)) (hi : i ∈ listLength.evalSet xs) :
    listGet.evalSet (naturalSquarePair ((listMap f).evalSet (naturalSquarePair z xs)) i) =
      f.evalSet (naturalSquarePair z (listGet.evalSet (naturalSquarePair xs i))) := by
  have hiω := IsTransitive.transitive _ (evalSet_natural listLength hxs) _ hi
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hz
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hxs
  obtain ⟨w, rfl⟩ := internalArithmeticVal_surjective hiω
  have hw : w < listLength.evalArithmetic v := by
    rw [internalArithmetic_lt, evalArithmetic_agreement]
    exact hi
  have h := congrArg internalArithmeticVal (evalArithmetic_listMap_get f u v w hw)
  simpa only [evalArithmetic_agreement, internalArithmeticVal_pair] using h

theorem mem_range_decodedNaturalList_map (f : PrimitiveProgram) {z xs : V}
    (hz : z ∈ (ω : V)) (hxs : xs ∈ (ω : V)) (x : V) :
    x ∈ SetTheory.range (decodedNaturalList ((listMap f).evalSet (naturalSquarePair z xs))) ↔
      ∃ y ∈ SetTheory.range (decodedNaturalList xs), x = f.evalSet (naturalSquarePair z y) := by
  rw [mem_range_decodedNaturalList, evalSet_listMap_length f hz hxs]
  constructor
  · rintro ⟨i, hi, he⟩
    refine ⟨listGet.evalSet (naturalSquarePair xs i), (mem_range_decodedNaturalList _ _).mpr ⟨i, hi, rfl⟩, ?_⟩
    rw [evalSet_listMap_get f hz hxs hi] at he
    exact he
  · rintro ⟨y, hy, he⟩
    obtain ⟨i, hi, rfl⟩ := (mem_range_decodedNaturalList _ _).mp hy
    exact ⟨i, hi, he.trans (evalSet_listMap_get f hz hxs hi).symm⟩

theorem evalSet_listAppend_zero {ys : V} (hys : ys ∈ (ω : V)) :
    listAppend.evalSet (naturalSquarePair ys 0) = ys := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hys
  have h := congrArg internalArithmeticVal (evalArithmetic_listAppend_zero u)
  simpa only [evalArithmetic_agreement, internalArithmeticVal_pair, internalArithmeticVal_zero] using h

theorem evalSet_listAppend_cons {ys x xs : V}
    (hys : ys ∈ (ω : V)) (hx : x ∈ (ω : V)) (hxs : xs ∈ (ω : V)) :
    listAppend.evalSet (naturalSquarePair ys (SetTheory.succ (naturalSquarePair x xs))) =
      SetTheory.succ (naturalSquarePair x (listAppend.evalSet (naturalSquarePair ys xs))) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hys
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hx
  obtain ⟨w, rfl⟩ := internalArithmeticVal_surjective hxs
  have h := congrArg internalArithmeticVal (evalArithmetic_listAppend_cons u v w)
  simpa only [evalArithmetic_agreement, internalArithmeticVal_pair, internalArithmeticVal_succ] using h

theorem evalSet_listAppend_length {xs ys : V} (hxs : xs ∈ (ω : V)) (hys : ys ∈ (ω : V)) :
    listLength.evalSet (listAppend.evalSet (naturalSquarePair ys xs)) =
      ordinalAdd (listLength.evalSet xs) (listLength.evalSet ys) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hxs
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hys
  have h := congrArg internalArithmeticVal (evalArithmetic_listAppend_length u v)
  simpa only [evalArithmetic_agreement, internalArithmeticVal_pair, internalArithmeticVal_add] using h

end ZFVP
