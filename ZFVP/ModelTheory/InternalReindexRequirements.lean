import ZFVP.ModelTheory.InternalReindexSubstitution
import ZFVP.ModelTheory.InternalPrefixProgram
import ZFVP.Syntax.PrimitiveProgramReindexRequirements

/-! Internal syntax-check preservation for renaming and parameter-prefix programs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem requirementFits_reindexCode_depth {r m d c : V}
    (hr : r ∈ (ω : V)) (hm : m ∈ (ω : V)) (hd : d ∈ (ω : V)) (hc : c ∈ (ω : V))
    (hR : ∀ j ∈ listLength.evalSet r, listGet.evalSet (naturalSquarePair r j) ∈ m)
    (hv : requirementFits ((formulaRequirement false).evalSet c) (reindexSource r d)) :
    requirementFits ((formulaRequirement false).evalSet
      (reindexCode.evalSet (naturalSquarePair r (naturalSquarePair d c)))) (ordinalAdd m d) := by
  obtain ⟨r₀, rfl⟩ := internalArithmeticVal_surjective hr
  obtain ⟨m₀, rfl⟩ := internalArithmeticVal_surjective hm
  obtain ⟨d₀, rfl⟩ := internalArithmeticVal_surjective hd
  obtain ⟨c₀, rfl⟩ := internalArithmeticVal_surjective hc
  have hR' : ∀ j < listLength.evalArithmetic r₀, listGet.evalArithmetic (Arithmetic.pair r₀ j) < m₀ := by
    intro j hj
    apply (internalArithmetic_lt _ _).mpr
    rw [evalArithmetic_agreement, internalArithmeticVal_pair]
    apply hR
    rw [← evalArithmetic_agreement, ← internalArithmetic_lt]
    exact hj
  have hv' : (formulaRequirement false).evalArithmetic c₀ ≠ 0 ∧
      (formulaRequirement false).evalArithmetic c₀ ≤ (listLength.evalArithmetic r₀ + d₀) + 1 := by
    rw [← requirementFits_val, evalArithmetic_agreement, internalArithmeticVal_add, evalArithmetic_agreement]
    exact hv
  have h := (requirementFits_val _ _).mpr (reindexCode_requirement hR' c₀ d₀ hv')
  simpa only [evalArithmetic_agreement, internalArithmeticVal_pair, internalArithmeticVal_add] using h

theorem requirementFits_reindexCode {r m c : V}
    (hr : r ∈ (ω : V)) (hm : m ∈ (ω : V)) (hc : c ∈ (ω : V))
    (hR : decodedNaturalList r ∈ m ^ listLength.evalSet r)
    (hv : requirementFits ((formulaRequirement false).evalSet c) (listLength.evalSet r)) :
    requirementFits ((formulaRequirement false).evalSet
      (reindexCode.evalSet (naturalSquarePair r (naturalSquarePair 0 c)))) m := by
  have hR' : ∀ j ∈ listLength.evalSet r, listGet.evalSet (naturalSquarePair r j) ∈ m := by
    intro j hj
    rw [← value_decodedNaturalList hj]
    exact function_value_mem hR hj
  have h0 : (0 : V) ∈ (ω : V) := by simp
  have hv' : requirementFits ((formulaRequirement false).evalSet c) (reindexSource r 0) := by
    rwa [reindexSource_zero]
  have h := requirementFits_reindexCode_depth hr hm h0 hc hR' hv'
  simpa only [zero_def, ordinalAdd_zero] using h

theorem decodedNaturalFormula_prefixProgram {a m : ℕ} (r : Fin a → Fin m) {n c : V}
    (hn : n ∈ (ω : V)) (hc : c ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement false).evalSet c) (prefixSize a n)) :
    decodedNaturalFormula (reindexCode.evalSet (naturalSquarePair
      ((PrimitiveProgram.prefixRenaming r).evalSet n) (naturalSquarePair 0 c))) =
      renameMembershipFormula (prefixSize a n) (prefixSize m n) (ZFVP.prefixRenaming r n) (decodedNaturalFormula c) := by
  have hR : decodedNaturalList ((PrimitiveProgram.prefixRenaming r).evalSet n) ∈
      prefixSize m n ^ listLength.evalSet ((PrimitiveProgram.prefixRenaming r).evalSet n) := by
    rw [decodedNaturalList_prefixRenaming r hn, evalSet_prefixRenaming_length r hn]
    exact prefixRenaming_function r hn
  have hv' : requirementFits ((formulaRequirement false).evalSet c)
      (listLength.evalSet ((PrimitiveProgram.prefixRenaming r).evalSet n)) := by
    rwa [evalSet_prefixRenaming_length r hn]
  have h := decodedNaturalFormula_reindex_rename (evalSet_natural _ hn) (prefixSize_natural m hn) hc hR hv'
  simpa only [evalSet_prefixRenaming_length r hn, decodedNaturalList_prefixRenaming r hn] using h

theorem requirementFits_prefixProgram {a m : ℕ} (r : Fin a → Fin m) {n c : V}
    (hn : n ∈ (ω : V)) (hc : c ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement false).evalSet c) (prefixSize a n)) :
    requirementFits ((formulaRequirement false).evalSet (reindexCode.evalSet (naturalSquarePair
      ((PrimitiveProgram.prefixRenaming r).evalSet n) (naturalSquarePair 0 c)))) (prefixSize m n) := by
  apply requirementFits_reindexCode (evalSet_natural _ hn) (prefixSize_natural m hn) hc
  · rw [decodedNaturalList_prefixRenaming r hn, evalSet_prefixRenaming_length r hn]
    exact prefixRenaming_function r hn
  · rwa [evalSet_prefixRenaming_length r hn]

end ZFVP
