import ZFVP.Syntax.PrimitiveProgramRequirementCharacterization

/-! Natural-code negation preserves syntax requirements at every internal input. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem formulaRequirement_negateCode (allowFree : Bool) (c : M) :
    (formulaRequirement allowFree).evalArithmetic (negateCode.evalArithmetic c) =
      (formulaRequirement allowFree).evalArithmetic c := by
  induction c using ISigma1.sigma1_order_induction
  · definability
  case ind c ih =>
    rcases listCode_cases c with (rfl | ⟨t, a, rfl⟩)
    · simp
    have ha : a < Arithmetic.pair t a + 1 := lt_succ_iff_le.mpr (le_pair_right t a)
    have hl : Arithmetic.pi₁ a < Arithmetic.pair t a + 1 := lt_of_le_of_lt (pi₁_le_self a) ha
    have hr : Arithmetic.pi₂ a < Arithmetic.pair t a + 1 := lt_of_le_of_lt (pi₂_le_self a) ha
    have iha := ih a ha
    have ihl := ih (Arithmetic.pi₁ a) hl
    have ihr := ih (Arithmetic.pi₂ a) hr
    by_cases h0 : t = 0
    · subst t; simp
    by_cases h1 : t = 1
    · subst t; simp
    by_cases h2 : t = 2
    · subst t; simp
    by_cases h3 : t = 3
    · subst t; simp
    by_cases h4 : t = 4
    · subst t
      have he := evalArithmetic_negateCode_and (Arithmetic.pi₁ a) (Arithmetic.pi₂ a)
      rw [Arithmetic.pair_unpair] at he
      rw [he, evalArithmetic_formulaRequirement_or, evalArithmetic_formulaRequirement_tagged]
      simp [formulaRequirementValue, ihl, ihr]
    by_cases h5 : t = 5
    · subst t
      have he := evalArithmetic_negateCode_or (Arithmetic.pi₁ a) (Arithmetic.pi₂ a)
      rw [Arithmetic.pair_unpair] at he
      rw [he, evalArithmetic_formulaRequirement_and, evalArithmetic_formulaRequirement_tagged]
      simp [formulaRequirementValue, ihl, ihr]
    by_cases h6 : t = 6
    · subst t; simp [iha]
    by_cases h7 : t = 7
    · subst t; simp [iha]
    · simp [evalArithmetic_negateCode, negateArithmeticStep,
        evalArithmetic_formulaRequirement_tagged, formulaRequirementValue, h0, h1, h2, h3, h4, h5, h6, h7]

end PrimitiveProgram
end ZFVP