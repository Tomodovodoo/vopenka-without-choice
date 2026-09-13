import ZFVP.ModelTheory.InternalProgramForwardTabulate
import ZFVP.ModelTheory.StandardProgramLists
import ZFVP.ModelTheory.NaturalSyntaxStandard
import ZFVP.Syntax.PrimitiveProgramPrefixRenaming

/-! Explicit parameter-prefix programs decode to the template compiler's internal renamings. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem evalSet_constant (k : ℕ) (x : V) : (constant k).evalSet x = (k : V) := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [constant, evalSet_comp, evalSet_succ, num_succ_def] using congrArg SetTheory.succ ih

theorem evalSet_identity {x : V} (hx : x ∈ (ω : V)) : identity.evalSet x = x := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hx
  rw [← evalArithmetic_agreement, evalArithmetic_identity]

theorem evalSet_listAppend_ofFn_length {n : ℕ} (v : Fin n → ℕ) {ys : V} (hys : ys ∈ (ω : V)) :
    listLength.evalSet (listAppend.evalSet (naturalSquarePair ys (Encodable.encode (List.ofFn v) : V))) =
      prefixSize n (listLength.evalSet ys) := by
  rw [evalSet_listAppend_length (by simp) hys, evalSet_listLength_encode, List.length_ofFn,
    ← prefixSize_eq_ordinalAdd n (evalSet_natural listLength hys)]

theorem decodedNaturalList_append_ofFn {n : ℕ} (v : Fin n → ℕ) {ys : V} (hys : ys ∈ (ω : V)) :
    decodedNaturalList (listAppend.evalSet (naturalSquarePair ys (Encodable.encode (List.ofFn v) : V))) =
      prependTuple (listLength.evalSet ys) (decodedNaturalList ys) (fun i ↦ (v i : V)) := by
  induction n with
  | zero =>
    simp only [List.ofFn_zero, Encodable.encode_list_nil, cast_zero_def, evalSet_listAppend_zero hys, prependTuple]
  | succ n ih =>
    rw [List.ofFn_succ, Encodable.encode_list_cons, Encodable.encode_nat, ← naturalCons_natCast,
      evalSet_listAppend_cons hys (by simp) (by simp), decodedNaturalList_cons (by simp)
        (evalSet_natural listAppend (naturalSquarePair_natural hys (by simp))),
      evalSet_listAppend_ofFn_length _ hys, ih]
    rfl

theorem evalSet_prefixRenaming {a m : ℕ} (r : Fin a → Fin m) {n : V} (hn : n ∈ (ω : V)) :
    (PrimitiveProgram.prefixRenaming r).evalSet n = listAppend.evalSet
      (naturalSquarePair ((forwardTabulate addition).evalSet (naturalSquarePair (m : V) n))
        (Encodable.encode (List.ofFn (fun i ↦ (r i).val)) : V)) := by
  simp only [PrimitiveProgram.prefixRenaming, evalSet_comp, evalSet_pair, evalSet_constant, evalSet_identity hn]

theorem evalSet_prefixRenaming_length {a m : ℕ} (r : Fin a → Fin m) {n : V} (hn : n ∈ (ω : V)) :
    listLength.evalSet ((PrimitiveProgram.prefixRenaming r).evalSet n) = prefixSize a n := by
  rw [evalSet_prefixRenaming r hn, evalSet_listAppend_ofFn_length _
    (evalSet_natural _ (naturalSquarePair_natural (by simp) hn)), evalSet_forwardTabulate_length addition (by simp) hn]

theorem decodedNaturalList_prefixRenaming {a m : ℕ} (r : Fin a → Fin m) {n : V} (hn : n ∈ (ω : V)) :
    decodedNaturalList ((PrimitiveProgram.prefixRenaming r).evalSet n) = ZFVP.prefixRenaming r n := by
  rw [evalSet_prefixRenaming r hn, decodedNaturalList_append_ofFn _
    (evalSet_natural _ (naturalSquarePair_natural (by simp) hn)),
    evalSet_forwardTabulate_length addition (by simp) hn, decodedNaturalList_forwardTabulate_skipIndices m hn]
  rfl

end ZFVP
