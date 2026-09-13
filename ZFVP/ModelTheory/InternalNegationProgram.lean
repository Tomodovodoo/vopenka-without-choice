import ZFVP.ModelTheory.NaturalFormulaRequirementInduction
import ZFVP.ModelTheory.InternalNegationProgramEquations
import ZFVP.Syntax.FormulaNegation
import ZFVP.Syntax.PrimitiveProgramNegationRequirements

/-! The explicit natural-code negation program agrees with internal formula negation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem decodedNaturalFormula_negateCode (allowFree : Bool) {c n : V}
    (hc : c ∈ (ω : V)) (hn : n ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement allowFree).evalSet c) n) :
    decodedNaturalFormula (negateCode.evalSet c) =
      negateFormula membershipLanguageCode (naturalSyntaxFreeDomain allowFree) n (decodedNaturalFormula c) := by
  apply naturalFormulaRequirement_induction allowFree
    (fun n c : V ↦ decodedNaturalFormula (negateCode.evalSet c) =
      negateFormula membershipLanguageCode (naturalSyntaxFreeDomain allowFree) n (decodedNaturalFormula c))
    (by definability) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hc hn hv
  · intro n a hn ha hv
    rw [evalSet_negateCode_rel ha, decodedNaturalFormula_nrel ha, decodedNaturalFormula_rel ha,
      negateFormula_atom membershipLanguageCode_valid hn (decodedNaturalAtomic_payload_valid allowFree ha hn hv)]
  · intro n a hn ha hv
    rw [evalSet_negateCode_nrel ha, decodedNaturalFormula_rel ha, decodedNaturalFormula_nrel ha,
      negateFormula_negAtom membershipLanguageCode_valid hn (decodedNaturalAtomic_payload_valid allowFree ha hn hv)]
  · intro n a hn ha
    rw [evalSet_negateCode_verum ha, decodedNaturalFormula_falsum (by simp), decodedNaturalFormula_verum ha,
      negateFormula_truth membershipLanguageCode_valid hn]
  · intro n a hn ha
    rw [evalSet_negateCode_falsum ha, decodedNaturalFormula_verum (by simp), decodedNaturalFormula_falsum ha,
      negateFormula_falsity membershipLanguageCode_valid hn]
  · intro n a b hn ha hb hva hvb iha ihb
    rw [evalSet_negateCode_and ha hb, decodedNaturalFormula_or (evalSet_natural negateCode ha) (evalSet_natural negateCode hb),
      decodedNaturalFormula_and ha hb, negateFormula_and membershipLanguageCode_valid hn
        (decodedNaturalFormula_valid allowFree ha hn hva) (decodedNaturalFormula_valid allowFree hb hn hvb), iha, ihb]
  · intro n a b hn ha hb hva hvb iha ihb
    rw [evalSet_negateCode_or ha hb, decodedNaturalFormula_and (evalSet_natural negateCode ha) (evalSet_natural negateCode hb),
      decodedNaturalFormula_or ha hb, negateFormula_or membershipLanguageCode_valid hn
        (decodedNaturalFormula_valid allowFree ha hn hva) (decodedNaturalFormula_valid allowFree hb hn hvb), iha, ihb]
  · intro n a hn ha hva iha
    rw [evalSet_negateCode_all ha, decodedNaturalFormula_exs (evalSet_natural negateCode ha),
      decodedNaturalFormula_all ha, negateFormula_all membershipLanguageCode_valid hn
        (decodedNaturalFormula_valid allowFree ha (ω_succ_closed hn) hva), iha]
  · intro n a hn ha hva iha
    rw [evalSet_negateCode_exs ha, decodedNaturalFormula_all (evalSet_natural negateCode ha),
      decodedNaturalFormula_exs ha, negateFormula_exists membershipLanguageCode_valid hn
        (decodedNaturalFormula_valid allowFree ha (ω_succ_closed hn) hva), iha]

theorem evalSet_formulaRequirement_negateCode (allowFree : Bool) {c : V} (hc : c ∈ (ω : V)) :
    (formulaRequirement allowFree).evalSet (negateCode.evalSet c) =
      (formulaRequirement allowFree).evalSet c := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hc
  simp only [← evalArithmetic_agreement, formulaRequirement_negateCode]

theorem requirementFits_negateCode (allowFree : Bool) {c n : V} (hc : c ∈ (ω : V)) :
    requirementFits ((formulaRequirement allowFree).evalSet (negateCode.evalSet c)) n ↔
      requirementFits ((formulaRequirement allowFree).evalSet c) n := by
  rw [evalSet_formulaRequirement_negateCode allowFree hc]

theorem decodedNaturalFormula_double_negateCode (allowFree : Bool) {c n : V}
    (hc : c ∈ (ω : V)) (hn : n ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement allowFree).evalSet c) n) :
    decodedNaturalFormula (negateCode.evalSet (negateCode.evalSet c)) = decodedNaturalFormula c := by
  rw [decodedNaturalFormula_negateCode allowFree (evalSet_natural negateCode hc) hn
      ((requirementFits_negateCode allowFree hc).mpr hv),
    decodedNaturalFormula_negateCode allowFree hc hn hv,
    negateFormula_involutive membershipLanguageCode_valid (decodedNaturalFormula_valid allowFree hc hn hv)]
end ZFVP