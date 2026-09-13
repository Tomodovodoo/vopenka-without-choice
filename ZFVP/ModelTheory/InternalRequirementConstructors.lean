import ZFVP.ModelTheory.InternalFormulaRequirements

/-! Syntax-check equivalences for Boolean connectives and quantifiers. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem requirementFits_formula_and (allowFree : Bool) {a b n : V}
    (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) (hn : n ∈ (ω : V)) :
    requirementFits ((formulaRequirement allowFree).evalSet (succ (naturalSquarePair 4 (naturalSquarePair a b)))) n ↔
      requirementFits ((formulaRequirement allowFree).evalSet a) n ∧
      requirementFits ((formulaRequirement allowFree).evalSet b) n := by
  rw [evalSet_formulaRequirement_tagged allowFree (show (4 : V) ∈ (ω : V) from ofNat_mem_ω 4)
    (naturalSquarePair_natural ha hb)]
  simp only [naturalFormulaRequirementValue, OfNat.ofNat, setNumeral_eq_iff,
    naturalSquareLeft, naturalSquareRight, naturalSquareUnpair_pair ha hb]
  norm_num only
  exact requirementFits_join (evalSet_natural _ ha) (evalSet_natural _ hb) hn

theorem requirementFits_formula_or (allowFree : Bool) {a b n : V}
    (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) (hn : n ∈ (ω : V)) :
    requirementFits ((formulaRequirement allowFree).evalSet (succ (naturalSquarePair 5 (naturalSquarePair a b)))) n ↔
      requirementFits ((formulaRequirement allowFree).evalSet a) n ∧
      requirementFits ((formulaRequirement allowFree).evalSet b) n := by
  rw [evalSet_formulaRequirement_tagged allowFree (show (5 : V) ∈ (ω : V) from ofNat_mem_ω 5)
    (naturalSquarePair_natural ha hb)]
  simp only [naturalFormulaRequirementValue, OfNat.ofNat, setNumeral_eq_iff,
    naturalSquareLeft, naturalSquareRight, naturalSquareUnpair_pair ha hb]
  norm_num only
  exact requirementFits_join (evalSet_natural _ ha) (evalSet_natural _ hb) hn

theorem requirementFits_formula_all (allowFree : Bool) {a n : V}
    (ha : a ∈ (ω : V)) (hn : n ∈ (ω : V)) :
    requirementFits ((formulaRequirement allowFree).evalSet (succ (naturalSquarePair 6 a))) n ↔
      requirementFits ((formulaRequirement allowFree).evalSet a) (succ n) := by
  rw [evalSet_formulaRequirement_tagged allowFree (show (6 : V) ∈ (ω : V) from ofNat_mem_ω 6) ha]
  simp only [naturalFormulaRequirementValue, OfNat.ofNat, setNumeral_eq_iff]
  norm_num only
  exact requirementFits_quantify (evalSet_natural _ ha) hn

theorem requirementFits_formula_exs (allowFree : Bool) {a n : V}
    (ha : a ∈ (ω : V)) (hn : n ∈ (ω : V)) :
    requirementFits ((formulaRequirement allowFree).evalSet (succ (naturalSquarePair 7 a))) n ↔
      requirementFits ((formulaRequirement allowFree).evalSet a) (succ n) := by
  rw [evalSet_formulaRequirement_tagged allowFree (show (7 : V) ∈ (ω : V) from ofNat_mem_ω 7) ha]
  simp only [naturalFormulaRequirementValue, OfNat.ofNat, setNumeral_eq_iff]
  norm_num only
  exact requirementFits_quantify (evalSet_natural _ ha) hn

end ZFVP
