import ZFVP.ModelTheory.InternalReindexLifting
import ZFVP.Syntax.SubstitutionExtensionality

/-! The explicit renaming program implements internal membership-formula renaming. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem reindexEnvironment_substitutionStates {r m d φ : V}
    (hr : r ∈ (ω : V)) (hm : m ∈ (ω : V)) (hd : d ∈ (ω : V))
    (hR : ∀ j ∈ listLength.evalSet r, listGet.evalSet (naturalSquarePair r j) ∈ m)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (reindexSource r d)) :
    (formulaSubstitutionGraph membershipLanguageCode ∅ (reindexEnvironment r)) ‘
        ⟨⟨reindexSource r d, φ⟩ₖ, d⟩ₖ =
      (formulaSubstitutionGraph membershipLanguageCode ∅
        (substitutionStates membershipLanguageCode ∅ (reindexState r m 0))) ‘
          ⟨⟨reindexSource r d, φ⟩ₖ, d⟩ₖ := by
  apply formulaSubstitutionGraph_eq_of_tables membershipLanguageCode_valid (reindexSource r) (by definability)
    (fun _ hk ↦ reindexSource_succ hr hk) ?_ ?_ _ _ hφ d hd rfl
  · intro k hk i hi
    have hiω := IsTransitive.transitive _ (reindexSource_natural hr hk) _ hi
    rw [reindexEnvironment_bound r hk, substitutionStates_reindexState hr hm hR k hk,
      reindexState, stateBound_code, reindexBoundTable_value _ _ hiω, finiteReindexBoundTable_value hi]
  · intro k hk i hi
    exact (not_mem_empty hi).elim

theorem decodedNaturalFormula_reindex_rename {r m c : V}
    (hr : r ∈ (ω : V)) (hm : m ∈ (ω : V)) (hc : c ∈ (ω : V))
    (hR : decodedNaturalList r ∈ m ^ listLength.evalSet r)
    (hv : requirementFits ((formulaRequirement false).evalSet c) (listLength.evalSet r)) :
    decodedNaturalFormula (reindexCode.evalSet (naturalSquarePair r (naturalSquarePair 0 c))) =
      renameMembershipFormula (listLength.evalSet r) m (decodedNaturalList r) (decodedNaturalFormula c) := by
  have h0 : (0 : V) ∈ (ω : V) := by simp [zero_def]
  have hn := evalSet_natural listLength hr
  have hφ := decodedNaturalFormula_valid false hc hn hv
  have hR' : ∀ j ∈ listLength.evalSet r, listGet.evalSet (naturalSquarePair r j) ∈ m := by
    intro j hj
    rw [← value_decodedNaturalList hj]
    exact function_value_mem hR hj
  have he := decodedNaturalFormula_reindex_substitution hr hc hn h0 hv
  have hφ' : decodedNaturalFormula c ∈ formulaSet membershipLanguageCode ∅ (reindexSource r 0) := by
    simpa only [reindexSource_zero, naturalSyntaxFreeDomain, Bool.false_eq_true, ite_false] using hφ
  have he' := reindexEnvironment_substitutionStates hr hm h0 hR' hφ'
  rw [reindexSource_zero, reindexState_zero hr hm hR] at he'
  rw [renameMembershipFormula, substituteFormula, stateSource_code]
  exact he.trans he'

theorem decodedNaturalFormula_reindex_mem {r m c : V}
    (hr : r ∈ (ω : V)) (hm : m ∈ (ω : V)) (hc : c ∈ (ω : V))
    (hR : decodedNaturalList r ∈ m ^ listLength.evalSet r)
    (hv : requirementFits ((formulaRequirement false).evalSet c) (listLength.evalSet r)) :
    decodedNaturalFormula (reindexCode.evalSet (naturalSquarePair r (naturalSquarePair 0 c))) ∈
      formulaSet membershipLanguageCode ∅ m := by
  rw [decodedNaturalFormula_reindex_rename hr hm hc hR hv]
  exact renameMembershipFormula_mem (evalSet_natural listLength hr) hm hR
    (decodedNaturalFormula_valid false hc (evalSet_natural listLength hr) hv)

theorem membershipSatisfies_decodedNaturalFormula_reindex {A r m c b : V}
    (hA : IsNonempty A) (hr : r ∈ (ω : V)) (hm : m ∈ (ω : V)) (hc : c ∈ (ω : V))
    (hR : decodedNaturalList r ∈ m ^ listLength.evalSet r)
    (hv : requirementFits ((formulaRequirement false).evalSet c) (listLength.evalSet r)) (hb : b ∈ A ^ m) :
    MembershipSatisfies A m
      (decodedNaturalFormula (reindexCode.evalSet (naturalSquarePair r (naturalSquarePair 0 c)))) b ↔
      MembershipSatisfies A (listLength.evalSet r) (decodedNaturalFormula c) (compose (decodedNaturalList r) b) := by
  rw [decodedNaturalFormula_reindex_rename hr hm hc hR hv]
  exact membershipSatisfies_rename hA (evalSet_natural listLength hr) hm hR
    (decodedNaturalFormula_valid false hc (evalSet_natural listLength hr) hv) hb

end ZFVP
