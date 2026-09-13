import ZFVP.ModelTheory.InternalAtomicRequirements

/-! Constructor equations for the set-theoretic interpretation of syntax requirements. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

@[simp] theorem internalArithmeticVal_natCast (n : ℕ) :
    internalArithmeticVal (n : InternalArithmetic V) = (n : V) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, internalArithmeticVal_succ, ih]
    rfl

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem internalArithmeticVal_ite (p : Prop) [Decidable p] (x y : InternalArithmetic V) :
    internalArithmeticVal (if p then x else y) =
      if p then internalArithmeticVal x else internalArithmeticVal y := by
  split <;> rfl
noncomputable def naturalFormulaRequirementValue (allowFree : Bool) (t c : V) (F : V → V) : V := by
  classical
  exact if t = 0 then (atomicRequirement allowFree).evalSet c
  else if t = 1 then (atomicRequirement allowFree).evalSet c
  else if t = 2 then 1
  else if t = 3 then 1
  else if t = 4 then joinRequirements.evalSet (naturalSquarePair (F (naturalSquareLeft c)) (F (naturalSquareRight c)))
  else if t = 5 then joinRequirements.evalSet (naturalSquarePair (F (naturalSquareLeft c)) (F (naturalSquareRight c)))
  else if t = 6 then quantifyRequirement.evalSet (F c)
  else if t = 7 then quantifyRequirement.evalSet (F c)
  else 0

theorem evalSet_formulaRequirement_tagged (allowFree : Bool) {t c : V}
    (ht : t ∈ (ω : V)) (hc : c ∈ (ω : V)) :
    (formulaRequirement allowFree).evalSet (SetTheory.succ (naturalSquarePair t c)) =
      naturalFormulaRequirementValue allowFree t c (formulaRequirement allowFree).evalSet := by
  classical
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective ht
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hc
  rw [← internalArithmeticVal_pair, ← internalArithmeticVal_succ, ← evalArithmetic_agreement,
    evalArithmetic_formulaRequirement_tagged]
  have htag (m : ℕ) : internalArithmeticVal u = (SetTheory.ofNat m : V) ↔ u = (m : InternalArithmetic V) := by
    change internalArithmeticVal u = (m : V) ↔ _
    rw [← internalArithmeticVal_natCast, ← internalArithmetic_eq]
  have hz : internalArithmeticVal (Zero.zero : InternalArithmetic V) = (SetTheory.ofNat 0 : V) := internalArithmeticVal_zero
  have ho : internalArithmeticVal (One.one : InternalArithmetic V) = (SetTheory.ofNat 1 : V) := internalArithmeticVal_one
  unfold naturalFormulaRequirementValue formulaRequirementValue
  simp only [internalArithmeticVal_ite, OfNat.ofNat, htag, Nat.cast_zero, Nat.cast_one,
    ← evalArithmetic_agreement, naturalSquareLeft, naturalSquareRight,
    naturalSquareUnpair_internalArithmeticVal, ← internalArithmeticVal_pair,
    hz, ho]
theorem evalSet_formulaRequirement_zero (allowFree : Bool) :
    (formulaRequirement allowFree).evalSet (0 : V) = 0 := by
  rw [← internalArithmeticVal_zero, ← evalArithmetic_agreement, evalArithmetic_formulaRequirement_zero]

end ZFVP