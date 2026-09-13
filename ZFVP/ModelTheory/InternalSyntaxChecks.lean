import ZFVP.ModelTheory.InternalProgramListRanges
import ZFVP.ModelTheory.InternalFormulaRequirements
import ZFVP.Syntax.PrimitiveProgramSyntaxChecks

/-! Boolean formula and sequent checks accept exactly the internal syntax requirements. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem evalSet_formulaCheck_eq_one (allowFree : Bool) {n c : V} (hn : n ∈ (ω : V)) (hc : c ∈ (ω : V)) :
    (formulaCheck allowFree).evalSet (naturalSquarePair n c) = 1 ↔
      requirementFits ((formulaRequirement allowFree).evalSet c) n := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hn
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hc
  rw [evalSet_pair_val, ← internalArithmeticVal_one, ← internalArithmetic_eq,
    ← evalArithmetic_agreement, requirementFits_val]
  exact evalArithmetic_formulaCheck_eq_one allowFree u v

theorem evalSet_formulaCheck_ne_zero (allowFree : Bool) {n c : V} (hn : n ∈ (ω : V)) (hc : c ∈ (ω : V)) :
    (formulaCheck allowFree).evalSet (naturalSquarePair n c) ≠ 0 ↔
      requirementFits ((formulaRequirement allowFree).evalSet c) n := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hn
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hc
  rw [evalSet_pair_val, ne_eq, ← internalArithmeticVal_zero, ← internalArithmetic_eq,
    ← evalArithmetic_agreement, requirementFits_val]
  exact evalArithmetic_formulaCheck_ne_zero allowFree u v

def naturalSequentFits (allowFree : Bool) (n xs : V) : Prop :=
  ∀ c ∈ SetTheory.range (decodedNaturalList xs), requirementFits ((formulaRequirement allowFree).evalSet c) n

instance naturalSequentFits_definable (allowFree : Bool) : ℒₛₑₜ-relation[V] (naturalSequentFits allowFree) := by
  unfold naturalSequentFits
  definability

theorem evalSet_sequentCheck_eq_one (allowFree : Bool) {n xs : V} (hn : n ∈ (ω : V)) (hxs : xs ∈ (ω : V)) :
    (sequentCheck allowFree).evalSet (naturalSquarePair n xs) = 1 ↔ naturalSequentFits allowFree n xs := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hn
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hxs
  rw [evalSet_pair_val, ← internalArithmeticVal_one, ← internalArithmetic_eq, evalArithmetic_sequentCheck_eq_one]
  constructor
  · intro h c hc
    obtain ⟨w, rfl⟩ := internalArithmeticVal_surjective (mem_decodedNaturalList_range_natural hxs hc)
    obtain ⟨i, hi, he⟩ := (mem_range_decodedNaturalList_val w v).mp hc
    rw [← evalArithmetic_agreement, requirementFits_val, he]
    exact h i hi
  · intro h i hi
    have hm := (mem_range_decodedNaturalList_val (listGet.evalArithmetic (Arithmetic.pair v i)) v).mpr ⟨i, hi, rfl⟩
    have hv := h _ hm
    rw [← evalArithmetic_agreement, requirementFits_val] at hv
    exact hv

theorem naturalSequentFits_decoded (allowFree : Bool) {n xs c : V}
    (hn : n ∈ (ω : V)) (hxs : xs ∈ (ω : V)) (hv : naturalSequentFits allowFree n xs)
    (hc : c ∈ SetTheory.range (decodedNaturalList xs)) :
    decodedNaturalFormula c ∈ formulaSet membershipLanguageCode (naturalSyntaxFreeDomain allowFree) n :=
  decodedNaturalFormula_valid allowFree (mem_decodedNaturalList_range_natural hxs hc) hn (hv c hc)

theorem naturalSequentFits_cons (allowFree : Bool) {n c cs : V} (hc : c ∈ (ω : V)) (hcs : cs ∈ (ω : V)) :
    naturalSequentFits allowFree n (SetTheory.succ (naturalSquarePair c cs)) ↔
      requirementFits ((formulaRequirement allowFree).evalSet c) n ∧ naturalSequentFits allowFree n cs := by
  simp only [naturalSequentFits, mem_range_decodedNaturalList_cons hc hcs, forall_eq_or_imp]

end ZFVP
