import ZFVP.ModelTheory.InternalClosedTemplateProgram
import ZFVP.Syntax.PrimitiveProgramGeneratedAxioms

/-! Internal equations for the explicit ZF+VP axiom enumerator. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem evalSet_templateOptionProgram_some {a : ℕ} (t : MembershipTemplate a 0) {k c φ : V}
    (hk : k ∈ (ω : V)) (hc : c ∈ (ω : V)) (hφ : φ ∈ (ω : V)) :
    (templateOptionProgram t).evalSet (naturalSquarePair k c) = SetTheory.succ φ ↔
      requirementFits ((formulaRequirement false).evalSet c) (prefixSize a k) ∧
      t.closedTailProgram.evalSet (naturalSquarePair k c) = φ := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hk
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hc
  obtain ⟨w, rfl⟩ := internalArithmeticVal_surjective hφ
  rw [evalSet_pair_val, ← internalArithmeticVal_succ, ← internalArithmetic_eq, evalArithmetic_templateOptionProgram_some]
  have h := requirementFits_val ((formulaRequirement false).evalArithmetic v) ((a : InternalArithmetic V) + u)
  rw [evalArithmetic_agreement, internalArithmeticVal_add, internalArithmeticVal_natCast,
    ← prefixSize_eq_ordinalAdd a hk] at h
  rw [← h, internalArithmetic_eq, evalArithmetic_agreement, internalArithmeticVal_pair]

noncomputable def naturalGeneratedAxiomValue (tag k c : V) : V := by
  classical
  exact if tag = 0 then (Encodable.encode Axiom.empty + 1 : ℕ)
  else if tag = 1 then (Encodable.encode Axiom.extentionality + 1 : ℕ)
  else if tag = 2 then (Encodable.encode Axiom.pairing + 1 : ℕ)
  else if tag = 3 then (Encodable.encode Axiom.union + 1 : ℕ)
  else if tag = 4 then (Encodable.encode Axiom.power + 1 : ℕ)
  else if tag = 5 then (Encodable.encode Axiom.infinity + 1 : ℕ)
  else if tag = 6 then (Encodable.encode Axiom.foundation + 1 : ℕ)
  else if tag = 7 then (Encodable.encode equalityBasisSentence + 1 : ℕ)
  else if tag = 8 then (templateOptionProgram separationTemplate).evalSet (naturalSquarePair k c)
  else if tag = 9 then (templateOptionProgram replacementTemplate).evalSet (naturalSquarePair k c)
  else if tag = 10 then (templateOptionProgram vopenkaTemplate).evalSet (naturalSquarePair 0 c)
  else 0

theorem arithmeticGeneratedAxiomValue_agreement (tag k c : InternalArithmetic V) :
    internalArithmeticVal (arithmeticGeneratedAxiomValue tag k c) =
      naturalGeneratedAxiomValue (internalArithmeticVal tag) (internalArithmeticVal k) (internalArithmeticVal c) := by
  have htag (n : ℕ) : internalArithmeticVal tag = (SetTheory.ofNat n : V) ↔ tag = (n : InternalArithmetic V) := by
    change internalArithmeticVal tag = (n : V) ↔ _
    rw [← internalArithmeticVal_natCast, ← internalArithmetic_eq]
  have hz : internalArithmeticVal (Zero.zero : InternalArithmetic V) = (SetTheory.ofNat 0 : V) := internalArithmeticVal_zero
  unfold arithmeticGeneratedAxiomValue naturalGeneratedAxiomValue
  simp only [internalArithmeticVal_ite, OfNat.ofNat, htag, Nat.cast_zero, Nat.cast_one,
    evalArithmetic_agreement, internalArithmeticVal_pair, hz, internalArithmeticVal_natCast, setNatCast_eq_ofNat]

theorem evalSet_generatedAxiomProgram {tag k c : V}
    (ht : tag ∈ (ω : V)) (hk : k ∈ (ω : V)) (hc : c ∈ (ω : V)) :
    generatedAxiomProgram.evalSet (naturalSquarePair tag (naturalSquarePair k c)) = naturalGeneratedAxiomValue tag k c := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective ht
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hk
  obtain ⟨w, rfl⟩ := internalArithmeticVal_surjective hc
  rw [← internalArithmeticVal_pair, evalSet_pair_val, evalArithmetic_generatedAxiomProgram,
    arithmeticGeneratedAxiomValue_agreement]

theorem evalSet_generatedAxiomCheck {φ e : V} (hφ : φ ∈ (ω : V)) (he : e ∈ (ω : V)) :
    generatedAxiomCheck.evalSet (naturalSquarePair φ e) = 1 ↔ generatedAxiomProgram.evalSet e = SetTheory.succ φ := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hφ
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective he
  rw [evalSet_pair_val, ← internalArithmeticVal_one, ← internalArithmetic_eq, evalArithmetic_generatedAxiomCheck,
    internalArithmetic_eq, internalArithmeticVal_succ, evalArithmetic_agreement]

end ZFVP
