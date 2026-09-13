import ZFVP.Syntax.PrimitiveProgramReindexVariables
import ZFVP.Syntax.PrimitiveProgramRequirementCharacterization

/-! Renaming preserves the explicit syntax checks at all internal arithmetic inputs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem reindexTerm_requirement {r m d c : M}
    (hR : ∀ j < listLength.evalArithmetic r, listGet.evalArithmetic (Arithmetic.pair r j) < m)
    (hv : (termRequirement false).evalArithmetic c ≠ 0 ∧
      (termRequirement false).evalArithmetic c ≤ (listLength.evalArithmetic r + d) + 1) :
    (termRequirement false).evalArithmetic (reindexTerm.evalArithmetic (Arithmetic.pair r (Arithmetic.pair d c))) ≠ 0 ∧
      (termRequirement false).evalArithmetic (reindexTerm.evalArithmetic (Arithmetic.pair r (Arithmetic.pair d c))) ≤ (m + d) + 1 := by
  rcases (termRequirement_valid_iff false _ _).mp hv with ⟨i, hi, rfl⟩ | ⟨hf, _⟩
  · rw [evalArithmetic_reindexTerm_bound, termRequirement_valid_iff]
    exact Or.inl ⟨arithmeticReindexVariable r d i, arithmeticReindexVariable_bound hR hi, rfl⟩
  · cases hf

theorem reindexArguments_requirement {r m d k rel c : M}
    (hR : ∀ j < listLength.evalArithmetic r, listGet.evalArithmetic (Arithmetic.pair r j) < m)
    (hv : (atomicRequirement false).evalArithmetic (Arithmetic.pair k (Arithmetic.pair rel c)) ≠ 0 ∧
      (atomicRequirement false).evalArithmetic (Arithmetic.pair k (Arithmetic.pair rel c)) ≤
        (listLength.evalArithmetic r + d) + 1) :
    (atomicRequirement false).evalArithmetic (Arithmetic.pair 2 (Arithmetic.pair rel
      (reindexArguments.evalArithmetic (Arithmetic.pair r (Arithmetic.pair d c))))) ≠ 0 ∧
    (atomicRequirement false).evalArithmetic (Arithmetic.pair 2 (Arithmetic.pair rel
      (reindexArguments.evalArithmetic (Arithmetic.pair r (Arithmetic.pair d c))))) ≤ (m + d) + 1 := by
  rw [atomicRequirement_valid_iff] at hv ⊢
  simp only [evalArithmetic_reindexArguments, evalArithmetic_listLength_cons, evalArithmetic_listLength_zero,
    zero_add, evalArithmetic_listHead_cons, evalArithmetic_listTail_cons]
  refine ⟨trivial, hv.2.1, ?_, ?_, ?_⟩
  · exact one_add_one_eq_two
  · simpa only [evalArithmetic_reindexTerm] using reindexTerm_requirement hR hv.2.2.2.1
  · simpa only [evalArithmetic_reindexTerm] using reindexTerm_requirement hR hv.2.2.2.2

theorem reindexCode_requirement {r m : M}
    (hR : ∀ j < listLength.evalArithmetic r, listGet.evalArithmetic (Arithmetic.pair r j) < m) (c d : M)
    (hv : (formulaRequirement false).evalArithmetic c ≠ 0 ∧
      (formulaRequirement false).evalArithmetic c ≤ (listLength.evalArithmetic r + d) + 1) :
    (formulaRequirement false).evalArithmetic (reindexCode.evalArithmetic (Arithmetic.pair r (Arithmetic.pair d c))) ≠ 0 ∧
      (formulaRequirement false).evalArithmetic (reindexCode.evalArithmetic (Arithmetic.pair r (Arithmetic.pair d c))) ≤ (m + d) + 1 := by
  induction c using ISigma1.pi1_order_induction generalizing d
  · definability
  case ind c ih =>
    rcases listCode_cases c with (rfl | ⟨t, a, rfl⟩)
    · simp at hv
    have ha : a < Arithmetic.pair t a + 1 := lt_succ_iff_le.mpr (le_pair_right t a)
    have hl : Arithmetic.pi₁ a < Arithmetic.pair t a + 1 := lt_of_le_of_lt (pi₁_le_self a) ha
    have hh : Arithmetic.pi₂ a < Arithmetic.pair t a + 1 := lt_of_le_of_lt (pi₂_le_self a) ha
    change (formulaRequirement false).evalArithmetic
        ((formulaTransformCode reindexArguments).evalArithmetic (Arithmetic.pair r (Arithmetic.pair d (Arithmetic.pair t a + 1)))) ≠ 0 ∧
      (formulaRequirement false).evalArithmetic
        ((formulaTransformCode reindexArguments).evalArithmetic (Arithmetic.pair r (Arithmetic.pair d (Arithmetic.pair t a + 1)))) ≤ (m + d) + 1
    by_cases h0 : t = 0
    · subst t
      simp only [evalArithmetic_formulaRequirement_rel] at hv
      simp only [evalArithmetic_formulaTransformCode_rel, evalArithmetic_formulaRequirement_rel]
      apply reindexArguments_requirement hR (k := Arithmetic.pi₁ a)
      simpa only [Arithmetic.pair_unpair] using hv
    by_cases h1 : t = 1
    · subst t
      simp only [evalArithmetic_formulaRequirement_nrel] at hv
      simp only [evalArithmetic_formulaTransformCode_nrel, evalArithmetic_formulaRequirement_nrel]
      apply reindexArguments_requirement hR (k := Arithmetic.pi₁ a)
      simpa only [Arithmetic.pair_unpair] using hv
    by_cases h2 : t = 2
    · subst t
      rw [evalArithmetic_formulaTransformCode_verum, evalArithmetic_formulaRequirement_verum]
      simp
    by_cases h3 : t = 3
    · subst t
      rw [evalArithmetic_formulaTransformCode_falsum, evalArithmetic_formulaRequirement_falsum]
      simp
    by_cases h4 : t = 4
    · subst t
      have he : Arithmetic.pair (Arithmetic.pi₁ a) (Arithmetic.pi₂ a) = a := Arithmetic.pair_unpair a
      rw [← he, evalArithmetic_formulaRequirement_and, joinRequirements_valid_iff] at hv
      rw [← he, evalArithmetic_formulaTransformCode_and, evalArithmetic_formulaRequirement_and, joinRequirements_valid_iff]
      exact ⟨ih _ hl d hv.1, ih _ hh d hv.2⟩
    by_cases h5 : t = 5
    · subst t
      have he : Arithmetic.pair (Arithmetic.pi₁ a) (Arithmetic.pi₂ a) = a := Arithmetic.pair_unpair a
      rw [← he, evalArithmetic_formulaRequirement_or, joinRequirements_valid_iff] at hv
      rw [← he, evalArithmetic_formulaTransformCode_or, evalArithmetic_formulaRequirement_or, joinRequirements_valid_iff]
      exact ⟨ih _ hl d hv.1, ih _ hh d hv.2⟩
    by_cases h6 : t = 6
    · subst t
      rw [evalArithmetic_formulaRequirement_all, quantifyRequirement_valid_iff] at hv
      rw [evalArithmetic_formulaTransformCode_all, evalArithmetic_formulaRequirement_all, quantifyRequirement_valid_iff]
      simpa only [add_assoc, reindexCode] using ih a ha (d + 1) (by simpa only [add_assoc] using hv)
    by_cases h7 : t = 7
    · subst t
      rw [evalArithmetic_formulaRequirement_exs, quantifyRequirement_valid_iff] at hv
      rw [evalArithmetic_formulaTransformCode_exs, evalArithmetic_formulaRequirement_exs, quantifyRequirement_valid_iff]
      simpa only [add_assoc, reindexCode] using ih a ha (d + 1) (by simpa only [add_assoc] using hv)
    · simp [evalArithmetic_formulaRequirement_tagged, formulaRequirementValue, h0, h1, h2, h3, h4, h5, h6, h7] at hv

end PrimitiveProgram
end ZFVP
