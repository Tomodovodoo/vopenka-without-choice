import ZFVP.ModelTheory.InternalProgramListMap
import ZFVP.Syntax.PrimitiveProgramForwardTabulate
import ZFVP.Syntax.PrefixTuples

/-! Increasing-index program tables decode to the corresponding internal functions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem evalSet_addition {x y : V} (hx : x ∈ (ω : V)) (hy : y ∈ (ω : V)) :
    addition.evalSet (naturalSquarePair x y) = ordinalAdd x y := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hx
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hy
  rw [evalSet_pair_val, evalArithmetic_addition, internalArithmeticVal_add]

theorem evalSet_forwardTabulate_length (f : PrimitiveProgram) {z n : V}
    (hz : z ∈ (ω : V)) (hn : n ∈ (ω : V)) :
    listLength.evalSet ((forwardTabulate f).evalSet (naturalSquarePair z n)) = n := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hz
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hn
  have h := congrArg internalArithmeticVal (evalArithmetic_forwardTabulate_length f u v)
  simpa only [evalArithmetic_agreement, internalArithmeticVal_pair] using h

theorem evalSet_forwardTabulate_get (f : PrimitiveProgram) {z n i : V}
    (hz : z ∈ (ω : V)) (hn : n ∈ (ω : V)) (hi : i ∈ n) :
    listGet.evalSet (naturalSquarePair ((forwardTabulate f).evalSet (naturalSquarePair z n)) i) =
      f.evalSet (naturalSquarePair z i) := by
  have hiω := IsTransitive.transitive _ hn _ hi
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hz
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hn
  obtain ⟨w, rfl⟩ := internalArithmeticVal_surjective hiω
  have h := congrArg internalArithmeticVal
    (evalArithmetic_forwardTabulate_get f u v w ((internalArithmetic_lt w v).mpr hi))
  simpa only [evalArithmetic_agreement, internalArithmeticVal_pair] using h

theorem prefixSize_eq_ordinalAdd (m : ℕ) {n : V} (hn : n ∈ (ω : V)) :
    prefixSize m n = ordinalAdd (m : V) n := by
  induction m with
  | zero => exact (ordinalAdd_zero_left_natural hn).symm
  | succ m ih =>
    rw [prefixSize, num_succ_def, ordinalAdd_succ_left_natural (by simp) hn, ih]

theorem decodedNaturalList_forwardTabulate_skipIndices (m : ℕ) {n : V} (hn : n ∈ (ω : V)) :
    decodedNaturalList ((forwardTabulate addition).evalSet (naturalSquarePair (m : V) n)) = skipIndices m n := by
  have hm : (m : V) ∈ (ω : V) := by simp
  have hlen := evalSet_forwardTabulate_length addition hm hn
  have hf : decodedNaturalList ((forwardTabulate addition).evalSet (naturalSquarePair (m : V) n)) ∈
      prefixSize m n ^ n := by
    unfold decodedNaturalList
    rw [hlen]
    apply definableGraph_mem_function_of_mapsTo
    intro i hi
    rw [evalSet_forwardTabulate_get addition hm hn hi, evalSet_addition hm (IsTransitive.transitive _ hn _ hi),
      ← prefixSize_eq_ordinalAdd m (IsTransitive.transitive _ hn _ hi)]
    exact prefixSize_mem_of_mem m hn hi
  apply function_eq_of_values hf (skipIndices_function m hn)
  intro i hi
  rw [value_decodedNaturalList (hlen.symm ▸ hi), evalSet_forwardTabulate_get addition hm hn hi,
    evalSet_addition hm (IsTransitive.transitive _ hn _ hi)]
  exact (prefixSize_eq_ordinalAdd m (IsTransitive.transitive _ hn _ hi)).symm.trans
    (value_definableGraph _ _ _ hi).symm

end ZFVP
