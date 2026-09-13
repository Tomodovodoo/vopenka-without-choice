import ZFVP.ModelTheory.InternalProgramListMap
import ZFVP.Syntax.PrimitiveProgramListMemberEquations

/-! Exact ranges of internally decoded list constructors and concatenations. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem mem_decodedNaturalList_range_natural {xs x : V} (hxs : xs ∈ (ω : V))
    (hx : x ∈ SetTheory.range (decodedNaturalList xs)) : x ∈ (ω : V) :=
  range_subset_of_mem_function (decodedNaturalList_mem_function hxs) x hx

theorem evalSet_listMember_cons_iff {x y ys : V}
    (hx : x ∈ (ω : V)) (hy : y ∈ (ω : V)) (hys : ys ∈ (ω : V)) :
    listMember.evalSet (naturalSquarePair x (SetTheory.succ (naturalSquarePair y ys))) = 1 ↔
      x = y ∨ listMember.evalSet (naturalSquarePair x ys) = 1 := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hx
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hy
  obtain ⟨w, rfl⟩ := internalArithmeticVal_surjective hys
  simpa only [internalArithmetic_eq, evalArithmetic_agreement, internalArithmeticVal_pair,
    internalArithmeticVal_succ, internalArithmeticVal_one] using evalArithmetic_listMember_cons_iff u v w

theorem evalSet_listMember_append_iff {x xs ys : V}
    (hx : x ∈ (ω : V)) (hxs : xs ∈ (ω : V)) (hys : ys ∈ (ω : V)) :
    listMember.evalSet (naturalSquarePair x (listAppend.evalSet (naturalSquarePair ys xs))) = 1 ↔
      listMember.evalSet (naturalSquarePair x xs) = 1 ∨ listMember.evalSet (naturalSquarePair x ys) = 1 := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hx
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hxs
  obtain ⟨w, rfl⟩ := internalArithmeticVal_surjective hys
  simpa only [internalArithmetic_eq, evalArithmetic_agreement, internalArithmeticVal_pair,
    internalArithmeticVal_one] using evalArithmetic_listMember_append_iff u v w

theorem mem_range_decodedNaturalList_cons {y ys : V} (hy : y ∈ (ω : V)) (hys : ys ∈ (ω : V)) (x : V) :
    x ∈ SetTheory.range (decodedNaturalList (SetTheory.succ (naturalSquarePair y ys))) ↔
      x = y ∨ x ∈ SetTheory.range (decodedNaturalList ys) := by
  have hcons := ω_succ_closed (naturalSquarePair_natural hy hys)
  have h (hx : x ∈ (ω : V)) :
      x ∈ SetTheory.range (decodedNaturalList (SetTheory.succ (naturalSquarePair y ys))) ↔
        x = y ∨ x ∈ SetTheory.range (decodedNaturalList ys) := by
    rw [← evalSet_listMember_iff hx hcons, evalSet_listMember_cons_iff hx hy hys, evalSet_listMember_iff hx hys]
  constructor
  · intro hx
    exact (h (mem_decodedNaturalList_range_natural hcons hx)).mp hx
  · intro hx
    have hxω : x ∈ (ω : V) := hx.elim (fun he ↦ he ▸ hy) (mem_decodedNaturalList_range_natural hys)
    exact (h hxω).mpr hx

theorem mem_range_decodedNaturalList_append {xs ys : V} (hxs : xs ∈ (ω : V)) (hys : ys ∈ (ω : V)) (x : V) :
    x ∈ SetTheory.range (decodedNaturalList (listAppend.evalSet (naturalSquarePair ys xs))) ↔
      x ∈ SetTheory.range (decodedNaturalList xs) ∨ x ∈ SetTheory.range (decodedNaturalList ys) := by
  have happ := evalSet_natural listAppend (naturalSquarePair_natural hys hxs)
  have h (hx : x ∈ (ω : V)) :
      x ∈ SetTheory.range (decodedNaturalList (listAppend.evalSet (naturalSquarePair ys xs))) ↔
        x ∈ SetTheory.range (decodedNaturalList xs) ∨ x ∈ SetTheory.range (decodedNaturalList ys) := by
    rw [← evalSet_listMember_iff hx happ, evalSet_listMember_append_iff hx hxs hys,
      evalSet_listMember_iff hx hxs, evalSet_listMember_iff hx hys]
  constructor
  · intro hx
    exact (h (mem_decodedNaturalList_range_natural happ hx)).mp hx
  · intro hx
    have hxω := hx.elim (mem_decodedNaturalList_range_natural hxs) (mem_decodedNaturalList_range_natural hys)
    exact (h hxω).mpr hx

@[simp] theorem range_decodedNaturalList_zero : SetTheory.range (decodedNaturalList (0 : V)) = ∅ := by
  have hlen : listLength.evalSet (0 : V) = 0 := by
    have h := congrArg internalArithmeticVal (evalArithmetic_listLength_zero (M := InternalArithmetic V))
    simpa only [evalArithmetic_agreement, internalArithmeticVal_zero] using h
  apply SetTheory.mem_ext
  intro x
  rw [mem_range_decodedNaturalList, hlen]
  simp [zero_def]

end ZFVP
