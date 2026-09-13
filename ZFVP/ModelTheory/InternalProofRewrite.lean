import ZFVP.ModelTheory.InternalProofRewriteArguments
import ZFVP.ModelTheory.InternalFormulaTransformSubstitution

/-! The common formula-transformer results specialized to the explicit proof-rule rewrite. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem proofRewriteArguments_agree (allowFree : Bool) {s : V} (hs : s ∈ (ω : V)) :
    FormulaTransformArgumentsAgree proofRewriteArguments allowFree s (proofRewriteEnvironment s) := by
  intro d k r c n hd hk hr hc hn hv
  rw [proofRewriteEnvironment_bound s hd, proofRewriteEnvironment_free s hd]
  exact decodedNaturalArguments_proofRewrite_substitution allowFree hs hd hk hr hc hn hv

theorem decodedNaturalFormula_proofRewrite_rel (allowFree : Bool) {s d k r c n : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V))
    (hk : k ∈ (ω : V)) (hr : r ∈ (ω : V)) (hc : c ∈ (ω : V)) (hn : n ∈ (ω : V))
    (hv : requirementFits ((atomicRequirement allowFree).evalSet (naturalSquarePair k (naturalSquarePair r c))) n) :
    decodedNaturalFormula (proofRewriteCode.evalSet (naturalSquarePair s
      (naturalSquarePair d (succ (naturalSquarePair 0 (naturalSquarePair k (naturalSquarePair r c))))))) =
      (formulaSubstitutionGraph membershipLanguageCode (naturalSyntaxFreeDomain allowFree) (proofRewriteEnvironment s)) ‘
        ⟨⟨n, decodedNaturalFormula (succ (naturalSquarePair 0 (naturalSquarePair k (naturalSquarePair r c))))⟩ₖ, d⟩ₖ := by
  exact decodedNaturalFormula_formulaTransform_rel proofRewriteArguments allowFree (proofRewriteEnvironment s)
    (proofRewriteArguments_agree allowFree hs) hs hd hk hr hc hn hv

theorem decodedNaturalFormula_proofRewrite_nrel (allowFree : Bool) {s d k r c n : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V))
    (hk : k ∈ (ω : V)) (hr : r ∈ (ω : V)) (hc : c ∈ (ω : V)) (hn : n ∈ (ω : V))
    (hv : requirementFits ((atomicRequirement allowFree).evalSet (naturalSquarePair k (naturalSquarePair r c))) n) :
    decodedNaturalFormula (proofRewriteCode.evalSet (naturalSquarePair s
      (naturalSquarePair d (succ (naturalSquarePair 1 (naturalSquarePair k (naturalSquarePair r c))))))) =
      (formulaSubstitutionGraph membershipLanguageCode (naturalSyntaxFreeDomain allowFree) (proofRewriteEnvironment s)) ‘
        ⟨⟨n, decodedNaturalFormula (succ (naturalSquarePair 1 (naturalSquarePair k (naturalSquarePair r c))))⟩ₖ, d⟩ₖ := by
  exact decodedNaturalFormula_formulaTransform_nrel proofRewriteArguments allowFree (proofRewriteEnvironment s)
    (proofRewriteArguments_agree allowFree hs) hs hd hk hr hc hn hv

theorem decodedNaturalFormula_proofRewrite_substitution (allowFree : Bool) {s c n d : V}
    (hs : s ∈ (ω : V)) (hc : c ∈ (ω : V)) (hn : n ∈ (ω : V)) (hd : d ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement allowFree).evalSet c) n) :
    decodedNaturalFormula (proofRewriteCode.evalSet (naturalSquarePair s (naturalSquarePair d c))) =
      (formulaSubstitutionGraph membershipLanguageCode (naturalSyntaxFreeDomain allowFree) (proofRewriteEnvironment s)) ‘
        ⟨⟨n, decodedNaturalFormula c⟩ₖ, d⟩ₖ := by
  exact decodedNaturalFormula_formulaTransform_substitution proofRewriteArguments allowFree (proofRewriteEnvironment s)
    (proofRewriteArguments_agree allowFree hs) hs hc hn hd hv

end ZFVP
