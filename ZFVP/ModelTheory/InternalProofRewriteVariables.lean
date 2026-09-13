import ZFVP.ModelTheory.InternalProofRewrite
import ZFVP.Syntax.PrimitiveProgramProofRewriteVariables

/-! Decoded variable equations on arbitrary internal indices. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem naturalProofRewriteTerm_bound_zeroMode {d i : V} (hd : d ∈ (ω : V)) (hi : i ∈ (ω : V)) :
    naturalProofRewriteTerm 0 d (SetTheory.succ (naturalSquarePair 0 i)) = boundVarCode i := by
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hd
  obtain ⟨w, rfl⟩ := internalArithmeticVal_surjective hi
  have h := congrArg internalArithmeticVal (evalArithmetic_proofRewriteTerm_bound_zeroMode v w)
  simp only [evalArithmetic_agreement, internalArithmeticVal_succ, internalArithmeticVal_pair,
    internalArithmeticVal_zero] at h
  rw [naturalProofRewriteTerm, h, decodedNaturalTerm_bound hi]

theorem naturalProofRewriteTerm_bound_below {s d i : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) (hi : i ∈ d) :
    naturalProofRewriteTerm s d (SetTheory.succ (naturalSquarePair 0 i)) = boundVarCode i := by
  have hiω := IsTransitive.transitive _ hd _ hi
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hs
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hd
  obtain ⟨w, rfl⟩ := internalArithmeticVal_surjective hiω
  have h := congrArg internalArithmeticVal
    (evalArithmetic_proofRewriteTerm_bound_below u ((internalArithmetic_lt w v).mpr hi))
  simp only [evalArithmetic_agreement, internalArithmeticVal_succ, internalArithmeticVal_pair,
    internalArithmeticVal_zero] at h
  rw [naturalProofRewriteTerm, h, decodedNaturalTerm_bound hiω]

theorem naturalProofRewriteTerm_bound_edge {s d : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) (hs0 : s ≠ 0) :
    naturalProofRewriteTerm s d (SetTheory.succ (naturalSquarePair 0 d)) =
      freeVarCode (proofRewriteFreshIndex.evalSet s) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hs
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hd
  have hu : u ≠ 0 := by
    intro he
    exact hs0 (by rw [he, internalArithmeticVal_zero])
  have h := congrArg internalArithmeticVal (evalArithmetic_proofRewriteTerm_bound_edge hu v)
  simp only [← evalArithmetic_proofRewriteFreshIndex] at h
  simp only [evalArithmetic_agreement, internalArithmeticVal_succ, internalArithmeticVal_pair,
    internalArithmeticVal_zero, internalArithmeticVal_one] at h
  rw [naturalProofRewriteTerm, h, decodedNaturalTerm_free (evalSet_natural _ hs)]

theorem naturalProofRewriteTerm_free {s d i : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) (hi : i ∈ (ω : V)) :
    naturalProofRewriteTerm s d (SetTheory.succ (naturalSquarePair 1 i)) =
      freeVarCode (proofRewriteFreeIndex.evalSet (naturalSquarePair s i)) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hs
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hd
  obtain ⟨w, rfl⟩ := internalArithmeticVal_surjective hi
  have h := congrArg internalArithmeticVal (evalArithmetic_proofRewriteTerm_free u v w)
  simp only [← evalArithmetic_proofRewriteFreeIndex] at h
  simp only [evalArithmetic_agreement, internalArithmeticVal_succ, internalArithmeticVal_pair,
    internalArithmeticVal_one] at h
  rw [naturalProofRewriteTerm, h,
    decodedNaturalTerm_free (evalSet_natural _ (naturalSquarePair_natural hs hi))]

end ZFVP
