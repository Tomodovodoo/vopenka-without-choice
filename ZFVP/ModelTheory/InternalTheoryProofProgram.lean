import ZFVP.Syntax.PrimitiveProgramTheoryProof
import ZFVP.ModelTheory.InternalGeneratedAxiomSoundness
import ZFVP.ModelTheory.InternalLKCertificateSoundness

/-! Internal equations for the generated-theory certificate checker. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem evalSet_generatedAxiomRowsCheck {z rows : V} (hz : z ∈ (ω : V)) (hrows : rows ∈ (ω : V)) :
    generatedAxiomRowsCheck.evalSet (naturalSquarePair z rows) = 1 ↔
      ∀ row ∈ range (decodedNaturalList rows), generatedAxiomCheck.evalSet row = 1 := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hz
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hrows
  rw [evalSet_pair_val, ← internalArithmeticVal_one, ← internalArithmetic_eq,
    evalArithmetic_generatedAxiomRowsCheck]
  constructor
  · intro h row hr
    obtain ⟨w, rfl⟩ := internalArithmeticVal_surjective (mem_decodedNaturalList_range_natural hrows hr)
    obtain ⟨i, hi, he⟩ := (mem_range_decodedNaturalList_val w v).mp hr
    rw [← evalArithmetic_agreement, ← internalArithmetic_eq, he]
    exact h i hi
  · intro h i hi
    have hr := (mem_range_decodedNaturalList_val (listGet.evalArithmetic (Arithmetic.pair v i)) v).mpr ⟨i, hi, rfl⟩
    have hv := h _ hr
    rw [← evalArithmetic_agreement, ← internalArithmetic_eq] at hv
    exact hv

theorem evalSet_negatedAxiomRow {z row : V} (hz : z ∈ (ω : V)) (hr : row ∈ (ω : V)) :
    negatedAxiomRow.evalSet (naturalSquarePair z row) = negateCode.evalSet (naturalSquareLeft row) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hz
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hr
  have h := congrArg internalArithmeticVal (evalArithmetic_negatedAxiomRow u v)
  simpa only [evalArithmetic_agreement, internalArithmeticVal_pair, naturalSquareLeft_val] using h

theorem evalSet_generatedTheorySequent {φ rows : V} (hφ : φ ∈ (ω : V)) (hr : rows ∈ (ω : V)) :
    generatedTheorySequent.evalSet (naturalSquarePair φ rows) =
      succ (naturalSquarePair φ ((listMap negatedAxiomRow).evalSet (naturalSquarePair 0 rows))) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hφ
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hr
  have h := congrArg internalArithmeticVal (evalArithmetic_generatedTheorySequent u v)
  simpa only [evalArithmetic_agreement, internalArithmeticVal_pair, internalArithmeticVal_zero,
    internalArithmeticVal_succ] using h

theorem evalSet_generatedTheoryProofCheck {φ rows p : V}
    (hφ : φ ∈ (ω : V)) (hr : rows ∈ (ω : V)) (hp : p ∈ (ω : V)) :
    generatedTheoryProofCheck.evalSet (naturalSquarePair φ (naturalSquarePair rows p)) = 1 ↔
      requirementFits ((formulaRequirement false).evalSet φ) 0 ∧
      generatedAxiomRowsCheck.evalSet (naturalSquarePair 0 rows) = 1 ∧
      lkProofCheck.evalSet (naturalSquarePair
        (generatedTheorySequent.evalSet (naturalSquarePair φ rows)) p) = 1 := by
  rw [← evalSet_formulaCheck_eq_one false (by simp [zero_def]) hφ]
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hφ
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hr
  obtain ⟨w, rfl⟩ := internalArithmeticVal_surjective hp
  simpa only [internalArithmetic_eq, evalArithmetic_agreement, internalArithmeticVal_pair,
    internalArithmeticVal_zero, internalArithmeticVal_one] using evalArithmetic_generatedTheoryProofCheck u v w

end ZFVP
