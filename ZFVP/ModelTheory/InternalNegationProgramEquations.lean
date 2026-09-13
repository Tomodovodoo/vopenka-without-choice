import ZFVP.ModelTheory.InternalFormulaRequirementEquations

/-! The explicit negation program's constructor equations on internal natural codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem setNatCast_eq_ofNat (n : ℕ) : (n : V) = SetTheory.ofNat n := rfl

@[simp] theorem evalSet_negateCode_rel {c : V} (hc : c ∈ (ω : V)) :
    negateCode.evalSet (SetTheory.succ (naturalSquarePair 0 c)) =
      SetTheory.succ (naturalSquarePair 1 c) := by
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hc
  have h := congrArg internalArithmeticVal (evalArithmetic_negateCode_rel v)
  simpa only [evalArithmetic_agreement, internalArithmeticVal_succ, internalArithmeticVal_pair,
    internalArithmeticVal_zero, internalArithmeticVal_one] using h

@[simp] theorem evalSet_negateCode_nrel {c : V} (hc : c ∈ (ω : V)) :
    negateCode.evalSet (SetTheory.succ (naturalSquarePair 1 c)) =
      SetTheory.succ (naturalSquarePair 0 c) := by
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hc
  have h := congrArg internalArithmeticVal (evalArithmetic_negateCode_nrel v)
  simpa only [evalArithmetic_agreement, internalArithmeticVal_succ, internalArithmeticVal_pair,
    internalArithmeticVal_zero, internalArithmeticVal_one] using h

@[simp] theorem evalSet_negateCode_verum {c : V} (hc : c ∈ (ω : V)) :
    negateCode.evalSet (SetTheory.succ (naturalSquarePair 2 c)) =
      SetTheory.succ (naturalSquarePair 3 0) := by
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hc
  have h := congrArg internalArithmeticVal (evalArithmetic_negateCode_verum v)
  simp only [evalArithmetic_agreement, internalArithmeticVal_succ, internalArithmeticVal_pair,
    internalArithmeticVal_zero] at h
  simpa only [OfNat.ofNat, internalArithmeticVal_natCast, setNatCast_eq_ofNat] using h

@[simp] theorem evalSet_negateCode_falsum {c : V} (hc : c ∈ (ω : V)) :
    negateCode.evalSet (SetTheory.succ (naturalSquarePair 3 c)) =
      SetTheory.succ (naturalSquarePair 2 0) := by
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hc
  have h := congrArg internalArithmeticVal (evalArithmetic_negateCode_falsum v)
  simp only [evalArithmetic_agreement, internalArithmeticVal_succ, internalArithmeticVal_pair,
    internalArithmeticVal_zero] at h
  simpa only [OfNat.ofNat, internalArithmeticVal_natCast, setNatCast_eq_ofNat] using h

@[simp] theorem evalSet_negateCode_and {a b : V} (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) :
    negateCode.evalSet (SetTheory.succ (naturalSquarePair 4 (naturalSquarePair a b))) =
      SetTheory.succ (naturalSquarePair 5 (naturalSquarePair (negateCode.evalSet a) (negateCode.evalSet b))) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective ha
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hb
  have h := congrArg internalArithmeticVal (evalArithmetic_negateCode_and u v)
  simp only [evalArithmetic_agreement, internalArithmeticVal_succ, internalArithmeticVal_pair] at h
  simpa only [OfNat.ofNat, internalArithmeticVal_natCast, setNatCast_eq_ofNat] using h

@[simp] theorem evalSet_negateCode_or {a b : V} (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) :
    negateCode.evalSet (SetTheory.succ (naturalSquarePair 5 (naturalSquarePair a b))) =
      SetTheory.succ (naturalSquarePair 4 (naturalSquarePair (negateCode.evalSet a) (negateCode.evalSet b))) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective ha
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hb
  have h := congrArg internalArithmeticVal (evalArithmetic_negateCode_or u v)
  simp only [evalArithmetic_agreement, internalArithmeticVal_succ, internalArithmeticVal_pair] at h
  simpa only [OfNat.ofNat, internalArithmeticVal_natCast, setNatCast_eq_ofNat] using h

@[simp] theorem evalSet_negateCode_all {a : V} (ha : a ∈ (ω : V)) :
    negateCode.evalSet (SetTheory.succ (naturalSquarePair 6 a)) =
      SetTheory.succ (naturalSquarePair 7 (negateCode.evalSet a)) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective ha
  have h := congrArg internalArithmeticVal (evalArithmetic_negateCode_all u)
  simp only [evalArithmetic_agreement, internalArithmeticVal_succ, internalArithmeticVal_pair] at h
  simpa only [OfNat.ofNat, internalArithmeticVal_natCast, setNatCast_eq_ofNat] using h

@[simp] theorem evalSet_negateCode_exs {a : V} (ha : a ∈ (ω : V)) :
    negateCode.evalSet (SetTheory.succ (naturalSquarePair 7 a)) =
      SetTheory.succ (naturalSquarePair 6 (negateCode.evalSet a)) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective ha
  have h := congrArg internalArithmeticVal (evalArithmetic_negateCode_exs u)
  simp only [evalArithmetic_agreement, internalArithmeticVal_succ, internalArithmeticVal_pair] at h
  simpa only [OfNat.ofNat, internalArithmeticVal_natCast, setNatCast_eq_ofNat] using h

end ZFVP