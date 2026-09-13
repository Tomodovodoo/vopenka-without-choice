import ZFVP.ModelTheory.InternalLKRuleSoundness
import ZFVP.ModelTheory.NaturalListCodeInduction
import ZFVP.Syntax.PrimitiveProgramLKCertificate

/-! Set-theoretic equations for the LK certificate program on all internal inputs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem naturalSquareLeft_val (x : InternalArithmetic V) :
    naturalSquareLeft (internalArithmeticVal x) = internalArithmeticVal (Arithmetic.pi₁ x) :=
  congrArg Prod.fst (naturalSquareUnpair_internalArithmeticVal x)

theorem naturalSquareRight_val (x : InternalArithmetic V) :
    naturalSquareRight (internalArithmeticVal x) = internalArithmeticVal (Arithmetic.pi₂ x) :=
  congrArg Prod.snd (naturalSquareUnpair_internalArithmeticVal x)

theorem evalSet_lkCertificateRun_zero {z : V} (hz : z ∈ (ω : V)) :
    PrimitiveProgram.lkCertificateRun.evalSet (naturalSquarePair z 0) = naturalSquarePair 0 1 := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hz
  have h := congrArg internalArithmeticVal (evalArithmetic_lkCertificateRun_zero u)
  simpa only [evalArithmetic_agreement, internalArithmeticVal_pair, internalArithmeticVal_zero,
    internalArithmeticVal_one] using h

theorem evalSet_lkCertificateRun_cons_left {z C w p : V}
    (hz : z ∈ (ω : V)) (hC : C ∈ (ω : V)) (hw : w ∈ (ω : V)) (hp : p ∈ (ω : V)) :
    naturalSquareLeft (PrimitiveProgram.lkCertificateRun.evalSet
      (naturalSquarePair z (SetTheory.succ (naturalSquarePair (naturalSquarePair C w) p)))) =
      SetTheory.succ (naturalSquarePair C
        (naturalSquareLeft (PrimitiveProgram.lkCertificateRun.evalSet (naturalSquarePair z p)))) := by
  obtain ⟨z₀, rfl⟩ := internalArithmeticVal_surjective hz
  obtain ⟨C₀, rfl⟩ := internalArithmeticVal_surjective hC
  obtain ⟨w₀, rfl⟩ := internalArithmeticVal_surjective hw
  obtain ⟨p₀, rfl⟩ := internalArithmeticVal_surjective hp
  have h := congrArg internalArithmeticVal (evalArithmetic_lkCertificateRun_cons_left z₀ C₀ w₀ p₀)
  simpa only [← naturalSquareLeft_val, evalArithmetic_agreement, internalArithmeticVal_pair,
    internalArithmeticVal_succ] using h

theorem evalSet_lkCertificateRun_cons_right_eq_one {z C w p : V}
    (hz : z ∈ (ω : V)) (hC : C ∈ (ω : V)) (hw : w ∈ (ω : V)) (hp : p ∈ (ω : V)) :
    naturalSquareRight (PrimitiveProgram.lkCertificateRun.evalSet
      (naturalSquarePair z (SetTheory.succ (naturalSquarePair (naturalSquarePair C w) p)))) = 1 ↔
      naturalSquareRight (PrimitiveProgram.lkCertificateRun.evalSet (naturalSquarePair z p)) = 1 ∧
        lkRuleCheck.evalSet (naturalSquarePair
          (naturalSquareLeft (PrimitiveProgram.lkCertificateRun.evalSet (naturalSquarePair z p)))
          (naturalSquarePair C w)) = 1 := by
  obtain ⟨z₀, rfl⟩ := internalArithmeticVal_surjective hz
  obtain ⟨C₀, rfl⟩ := internalArithmeticVal_surjective hC
  obtain ⟨w₀, rfl⟩ := internalArithmeticVal_surjective hw
  obtain ⟨p₀, rfl⟩ := internalArithmeticVal_surjective hp
  have h := evalArithmetic_lkCertificateRun_cons_right_eq_one z₀ C₀ w₀ p₀
  simpa only [internalArithmetic_eq, ← naturalSquareLeft_val, ← naturalSquareRight_val,
    evalArithmetic_agreement, internalArithmeticVal_pair, internalArithmeticVal_succ,
    internalArithmeticVal_one] using h

theorem evalSet_lkProofCheck_eq_one {C p : V} (hC : C ∈ (ω : V)) (hp : p ∈ (ω : V)) :
    lkProofCheck.evalSet (naturalSquarePair C p) = 1 ↔
      naturalSquareRight (PrimitiveProgram.lkCertificateRun.evalSet (naturalSquarePair 0 p)) = 1 ∧
        C ∈ SetTheory.range (decodedNaturalList
          (naturalSquareLeft (PrimitiveProgram.lkCertificateRun.evalSet (naturalSquarePair 0 p)))) := by
  obtain ⟨C₀, rfl⟩ := internalArithmeticVal_surjective hC
  obtain ⟨p₀, rfl⟩ := internalArithmeticVal_surjective hp
  have h := evalArithmetic_lkProofCheck_eq_one C₀ p₀
  simp only [internalArithmetic_eq, ← naturalSquareLeft_val, ← naturalSquareRight_val,
    evalArithmetic_agreement, internalArithmeticVal_pair, internalArithmeticVal_zero,
    internalArithmeticVal_one] at h
  rw [evalSet_listMember_iff (internalArithmeticVal_mem C₀) (naturalSquareLeft_natural _)] at h
  exact h

end ZFVP
