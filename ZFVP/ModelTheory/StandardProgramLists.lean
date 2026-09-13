import ZFVP.ModelTheory.InternalProgramLists
import ZFVP.Syntax.StandardLists

/-! The uniform internal list decoder agrees with standard finite lists. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

@[simp] theorem evalSet_listLength_encode (xs : List ℕ) :
    listLength.evalSet (Encodable.encode xs : V) = (xs.length : V) := by
  rw [evalSet_natCast, ← evalArithmetic_nat, evalArithmetic_listLength_encode]

theorem evalSet_listGet_encode (xs : List ℕ) (i : Fin xs.length) :
    listGet.evalSet (naturalSquarePair (Encodable.encode xs : V) (i.val : V)) = (xs.get i : V) := by
  rw [naturalSquarePair_natCast, evalSet_natCast, ← evalArithmetic_nat, ← arithmeticPair_nat,
    evalArithmetic_listGet_encode xs i.val i.isLt]
  rfl

theorem decodedNaturalList_encode_tuple (xs : List ℕ) :
    decodedNaturalList (Encodable.encode xs : V) = standardTuple (fun i : Fin xs.length ↦ (xs.get i : V)) := by
  apply mem_ext
  intro p
  rw [mem_decodedNaturalList, evalSet_listLength_encode, mem_standardTuple_iff]
  simp only [mem_natCast_iff]
  constructor
  · rintro ⟨j, ⟨i, rfl⟩, hp⟩
    exact ⟨i, by simpa only [evalSet_listGet_encode] using hp⟩
  · rintro ⟨i, hp⟩
    exact ⟨(i.val : V), ⟨i, rfl⟩, by simpa only [evalSet_listGet_encode] using hp⟩

end ZFVP
