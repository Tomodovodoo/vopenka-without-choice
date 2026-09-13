import ZFVP.ModelTheory.InternalProofRewriteLifting
import ZFVP.Syntax.SubstitutionExtensionality
import ZFVP.Syntax.FormulaSubstitutionSemantics

/-! The explicit natural rewrite program implements the actual capture-avoiding internal substitution. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem proofRewriteEnvironment_substitutionStates {s d φ : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ω (proofRewriteSource s d)) :
    (formulaSubstitutionGraph membershipLanguageCode ω (proofRewriteEnvironment s)) ‘
        ⟨⟨proofRewriteSource s d, φ⟩ₖ, d⟩ₖ =
      (formulaSubstitutionGraph membershipLanguageCode ω
        (substitutionStates membershipLanguageCode ω (proofRewriteState s 0))) ‘
          ⟨⟨proofRewriteSource s d, φ⟩ₖ, d⟩ₖ := by
  apply formulaSubstitutionGraph_eq_of_tables membershipLanguageCode_valid (proofRewriteSource s) (by definability)
    (fun _ _ ↦ proofRewriteSource_succ _ _) ?_ ?_ _ _ hφ d hd rfl
  · intro k hk i hi
    have hiω := IsTransitive.transitive _ (proofRewriteSource_natural s hk) _ hi
    rw [proofRewriteEnvironment_bound s hk, substitutionStates_proofRewriteState hs k hk,
      proofRewriteState, stateBound_code, proofRewriteVariableTable_value _ _ _ hiω, proofRewriteBoundTable_value hi]
  · intro k hk i hi
    rw [proofRewriteEnvironment_free s hk, substitutionStates_proofRewriteState hs k hk,
      proofRewriteState, stateFree_code]

theorem decodedNaturalFormula_proofRewrite_substitute {s c : V}
    (hs : s ∈ (ω : V)) (hc : c ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement true).evalSet c) (proofRewriteSource s 0)) :
    decodedNaturalFormula (proofRewriteCode.evalSet (naturalSquarePair s (naturalSquarePair 0 c))) =
      substituteFormula membershipLanguageCode ω ω (proofRewriteState s 0) (decodedNaturalFormula c) := by
  have h0 : (0 : V) ∈ (ω : V) := by simp [zero_def]
  have hn := proofRewriteSource_natural s h0
  have hφ : decodedNaturalFormula c ∈ formulaSet membershipLanguageCode ω (proofRewriteSource s 0) :=
    decodedNaturalFormula_valid true hc hn hv
  have he := decodedNaturalFormula_proofRewrite_substitution true hs hc hn h0 hv
  change decodedNaturalFormula (proofRewriteCode.evalSet (naturalSquarePair s (naturalSquarePair 0 c))) =
    (formulaSubstitutionGraph membershipLanguageCode ω (proofRewriteEnvironment s)) ‘
      ⟨⟨proofRewriteSource s 0, decodedNaturalFormula c⟩ₖ, (0 : V)⟩ₖ at he
  rw [substituteFormula, stateSource_proofRewriteState]
  exact he.trans (proofRewriteEnvironment_substitutionStates hs h0 hφ)

theorem decodedNaturalFormula_proofRewrite_mem {s c : V}
    (hs : s ∈ (ω : V)) (hc : c ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement true).evalSet c) (proofRewriteSource s 0)) :
    decodedNaturalFormula (proofRewriteCode.evalSet (naturalSquarePair s (naturalSquarePair 0 c))) ∈
      formulaSet (membershipLanguageCode : V) ω 0 := by
  have h0 : (0 : V) ∈ (ω : V) := by simp [zero_def]
  rw [decodedNaturalFormula_proofRewrite_substitute hs hc hv]
  have hφ := decodedNaturalFormula_valid true hc (proofRewriteSource_natural s h0) hv
  simpa only [stateTarget_proofRewriteState] using
    substituteFormula_mem membershipLanguageCode_valid (proofRewriteState_valid hs h0)
      (by simpa only [stateSource_proofRewriteState, naturalSyntaxFreeDomain, ite_true] using hφ)

theorem satisfies_decodedNaturalFormula_proofRewrite {s c M e b : V}
    (hM : IsStructureCode membershipLanguageCode M) (hs : s ∈ (ω : V)) (hc : c ∈ (ω : V))
    (he : e ∈ structureDomain M ^ (ω : V)) (hb : b ∈ structureDomain M ^ (0 : V))
    (hv : requirementFits ((formulaRequirement true).evalSet c) (proofRewriteSource s 0)) :
    Satisfies membershipLanguageCode ω M e 0
      (decodedNaturalFormula (proofRewriteCode.evalSet (naturalSquarePair s (naturalSquarePair 0 c)))) b ↔
    Satisfies membershipLanguageCode ω M
      (compose (proofRewriteVariableTable s 0 1) (termEvaluation membershipLanguageCode ω 0 M b e))
      (proofRewriteSource s 0) (decodedNaturalFormula c)
      (compose (proofRewriteBoundTable s 0) (termEvaluation membershipLanguageCode ω 0 M b e)) := by
  have h0 : (0 : V) ∈ (ω : V) := by simp [zero_def]
  rw [decodedNaturalFormula_proofRewrite_substitute hs hc hv]
  have hφ := decodedNaturalFormula_valid true hc (proofRewriteSource_natural s h0) hv
  simpa only [stateTarget_proofRewriteState, stateSource_proofRewriteState, stateBound_proofRewriteState,
    stateFree_proofRewriteState] using satisfies_substituteFormula hM (proofRewriteState_valid hs h0) he
      (by simpa only [stateSource_proofRewriteState, naturalSyntaxFreeDomain, ite_true] using hφ)
      (by simpa only [stateTarget_proofRewriteState] using hb)

end ZFVP
