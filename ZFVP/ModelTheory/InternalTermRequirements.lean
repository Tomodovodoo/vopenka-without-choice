import ZFVP.Syntax.PrimitiveProgramRequirementCharacterization
import ZFVP.ModelTheory.NaturalSyntaxStandard

/-! Accepted internal natural term codes decode to terms in their stated context. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def requirementFits (r n : V) : Prop := r ≠ 0 ∧ r ⊆ SetTheory.succ n

instance requirementFits_definable : ℒₛₑₜ-relation[V] requirementFits := by
  unfold requirementFits
  definability

theorem requirementFits_val (r n : InternalArithmetic V) :
    requirementFits (internalArithmeticVal r) (internalArithmeticVal n) ↔ r ≠ 0 ∧ r ≤ n + 1 := by
  unfold requirementFits
  rw [ne_eq, ← internalArithmeticVal_zero, ← internalArithmetic_eq,
    ← internalArithmeticVal_succ, ← internalArithmetic_le]

noncomputable def naturalSyntaxFreeDomain (allowFree : Bool) : V := if allowFree then ω else ∅

theorem decodedNaturalTerm_valid (allowFree : Bool) {c n : V} (hc : c ∈ (ω : V)) (hn : n ∈ (ω : V))
    (hv : requirementFits ((termRequirement allowFree).evalSet c) n) :
    decodedNaturalTerm c ∈ termSet membershipLanguageCode (naturalSyntaxFreeDomain allowFree) n := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hc
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hn
  rw [← evalArithmetic_agreement, requirementFits_val, termRequirement_valid_iff] at hv
  rcases hv with ⟨i, hi, he⟩ | ⟨ha, i, he⟩
  · have hvu := congrArg internalArithmeticVal he
    simp only [internalArithmeticVal_succ, internalArithmeticVal_pair, internalArithmeticVal_zero] at hvu
    rw [hvu, decodedNaturalTerm_bound (internalArithmeticVal_mem i)]
    exact (termSet_closed membershipLanguageCode_valid hn _).1 _ ((internalArithmetic_lt i v).mp hi)
  · have hvu := congrArg internalArithmeticVal he
    simp only [internalArithmeticVal_succ, internalArithmeticVal_pair, internalArithmeticVal_one] at hvu
    rw [hvu, decodedNaturalTerm_free (internalArithmeticVal_mem i)]
    apply (termSet_closed membershipLanguageCode_valid hn _).2.1
    simp only [naturalSyntaxFreeDomain, ha, ite_true]
    exact internalArithmeticVal_mem i

theorem requirementFits_join {x y n : V} (hx : x ∈ (ω : V)) (hy : y ∈ (ω : V)) (hn : n ∈ (ω : V)) :
    requirementFits (joinRequirements.evalSet (naturalSquarePair x y)) n ↔
      requirementFits x n ∧ requirementFits y n := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hx
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hy
  obtain ⟨w, rfl⟩ := internalArithmeticVal_surjective hn
  rw [evalSet_pair_val, requirementFits_val, requirementFits_val, requirementFits_val]
  exact joinRequirements_valid_iff _ _ _

theorem requirementFits_quantify {r n : V} (hr : r ∈ (ω : V)) (hn : n ∈ (ω : V)) :
    requirementFits (quantifyRequirement.evalSet r) n ↔ requirementFits r (SetTheory.succ n) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hr
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hn
  rw [← evalArithmetic_agreement, ← internalArithmeticVal_succ, requirementFits_val, requirementFits_val]
  exact quantifyRequirement_valid_iff _ _

end ZFVP