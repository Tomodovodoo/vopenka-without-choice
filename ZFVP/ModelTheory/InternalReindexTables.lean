import ZFVP.ModelTheory.InternalReindexVariables
import ZFVP.ModelTheory.InternalProofRewriteArguments

/-! Internal variable tables for the explicit bound-variable renaming program. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def naturalReindexTerm (r d c : V) : V :=
  decodedNaturalTerm (reindexTerm.evalSet (naturalSquarePair r (naturalSquarePair d c)))

instance naturalReindexTerm_definable : ℒₛₑₜ-function₃[V] naturalReindexTerm := by
  unfold naturalReindexTerm
  definability

noncomputable def reindexBoundTable (r d : V) : V :=
  definableGraph ω (fun i ↦ boundVarCode (naturalReindexVariable r d i)) (by definability)

instance reindexBoundTable_definable : ℒₛₑₜ-function₂[V] reindexBoundTable := by
  have h : ℒₛₑₜ-relation₃ (fun B r d : V ↦ ∀ p, p ∈ B ↔
      ∃ i ∈ (ω : V), p = ⟨i, boundVarCode (naturalReindexVariable r d i)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = reindexBoundTable (v 1) (v 2) ↔ _
  rw [SetTheory.mem_ext_iff]
  simp only [reindexBoundTable, mem_definableGraph_iff]

theorem reindexBoundTable_value (r d : V) {i : V} (hi : i ∈ (ω : V)) :
    (reindexBoundTable r d) ‘ i = boundVarCode (naturalReindexVariable r d i) :=
  value_definableGraph _ _ _ hi

noncomputable def reindexEnvironment (r : V) : V :=
  definableGraph ω (fun d ↦ substitutionState 0 0 (reindexBoundTable r d) ∅) (by definability)

instance reindexEnvironment_definable : ℒₛₑₜ-function₁[V] reindexEnvironment := by
  have h : ℒₛₑₜ-relation (fun G r : V ↦ ∀ p, p ∈ G ↔ ∃ d ∈ (ω : V),
      p = ⟨d, substitutionState 0 0 (reindexBoundTable r d) ∅⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = reindexEnvironment (v 1) ↔ _
  rw [SetTheory.mem_ext_iff]
  simp only [reindexEnvironment, mem_definableGraph_iff]

@[simp] theorem reindexEnvironment_bound (r : V) {d : V} (hd : d ∈ (ω : V)) :
    stateBound ((reindexEnvironment r) ‘ d) = reindexBoundTable r d := by
  rw [reindexEnvironment, value_definableGraph _ _ _ hd, stateBound_code]

@[simp] theorem reindexEnvironment_free (r : V) {d : V} (hd : d ∈ (ω : V)) :
    stateFree ((reindexEnvironment r) ‘ d) = ∅ := by
  rw [reindexEnvironment, value_definableGraph _ _ _ hd, stateFree_code]

theorem naturalReindexTerm_bound {r d i : V}
    (hr : r ∈ (ω : V)) (hd : d ∈ (ω : V)) (hi : i ∈ (ω : V)) :
    naturalReindexTerm r d (SetTheory.succ (naturalSquarePair 0 i)) = boundVarCode (naturalReindexVariable r d i) := by
  rw [naturalReindexTerm, evalSet_reindexTerm_bound hr hd hi,
    decodedNaturalTerm_bound (naturalReindexVariable_natural hr hd hi)]

theorem naturalReindexTerm_substitution {r d c n : V}
    (hr : r ∈ (ω : V)) (hd : d ∈ (ω : V)) (hc : c ∈ (ω : V)) (hn : n ∈ (ω : V))
    (hv : requirementFits ((termRequirement false).evalSet c) n) :
    naturalReindexTerm r d c =
      (termSubstitution membershipLanguageCode ∅ n (reindexBoundTable r d) ∅) ‘ (decodedNaturalTerm c) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hc
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hn
  rw [← evalArithmetic_agreement, requirementFits_val, termRequirement_valid_iff] at hv
  rcases hv with ⟨i, hi, he⟩ | ⟨hf, _, _⟩
  · have hcode := congrArg internalArithmeticVal he
    simp only [internalArithmeticVal_succ, internalArithmeticVal_pair, internalArithmeticVal_zero] at hcode
    rw [hcode, naturalReindexTerm_bound hr hd (internalArithmeticVal_mem i),
      decodedNaturalTerm_bound (internalArithmeticVal_mem i),
      termSubstitution_boundVar membershipLanguageCode_valid (internalArithmeticVal_mem v) _ _ _
        ((internalArithmetic_lt i v).mp hi), reindexBoundTable_value _ _ (internalArithmeticVal_mem i)]
  · cases hf

theorem evalSet_reindexArguments {r d c : V}
    (hr : r ∈ (ω : V)) (hd : d ∈ (ω : V)) (hc : c ∈ (ω : V)) :
    reindexArguments.evalSet (naturalSquarePair r (naturalSquarePair d c)) =
      SetTheory.succ (naturalSquarePair
        (reindexTerm.evalSet (naturalSquarePair r (naturalSquarePair d (listHead.evalSet c))))
        (SetTheory.succ (naturalSquarePair
          (reindexTerm.evalSet (naturalSquarePair r (naturalSquarePair d (listHead.evalSet (listTail.evalSet c))))) 0))) := by
  obtain ⟨r₀, rfl⟩ := internalArithmeticVal_surjective hr
  obtain ⟨d₀, rfl⟩ := internalArithmeticVal_surjective hd
  obtain ⟨c₀, rfl⟩ := internalArithmeticVal_surjective hc
  have h := congrArg internalArithmeticVal (evalArithmetic_reindexArguments r₀ d₀ c₀)
  simp only [← evalArithmetic_reindexTerm] at h
  simpa only [evalArithmetic_agreement, internalArithmeticVal_succ,
    internalArithmeticVal_pair, internalArithmeticVal_zero] using h

theorem decodedNaturalArguments_reindex {r d c : V}
    (hr : r ∈ (ω : V)) (hd : d ∈ (ω : V)) (hc : c ∈ (ω : V)) :
    decodedNaturalArguments (reindexArguments.evalSet (naturalSquarePair r (naturalSquarePair d c))) =
      standardTuple ![naturalReindexTerm r d (listHead.evalSet c),
        naturalReindexTerm r d (listHead.evalSet (listTail.evalSet c))] := by
  rw [evalSet_reindexArguments hr hd hc, decodedNaturalArguments_two
    (evalSet_natural _ (naturalSquarePair_natural hr (naturalSquarePair_natural hd (evalSet_natural _ hc))))
    (evalSet_natural _ (naturalSquarePair_natural hr
      (naturalSquarePair_natural hd (evalSet_natural _ (evalSet_natural _ hc)))))]
  rfl

theorem reindexArguments_agree {r : V} (hr : r ∈ (ω : V)) :
    FormulaTransformArgumentsAgree reindexArguments false r (reindexEnvironment r) := by
  intro d k rel c n hd hk hrel hc hn hv
  have hv' := atomicRequirement_term_fits false hk hrel hc hn hv
  have ha := evalSet_natural listHead hc
  have hb := evalSet_natural listHead (evalSet_natural listTail hc)
  rw [reindexEnvironment_bound r hd, reindexEnvironment_free r hd, decodedNaturalArguments_reindex hr hd hc]
  unfold decodedNaturalArguments
  rw [compose_standardTuple _ _ (fun i ↦ by
    rw [domain_termSubstitution]
    fin_cases i
    · exact decodedNaturalTerm_valid false ha hn hv'.1
    · exact decodedNaturalTerm_valid false hb hn hv'.2)]
  apply congrArg standardTuple
  funext i
  fin_cases i
  · exact naturalReindexTerm_substitution hr hd ha hn hv'.1
  · exact naturalReindexTerm_substitution hr hd hb hn hv'.2

theorem decodedNaturalFormula_reindex_substitution {r c n d : V}
    (hr : r ∈ (ω : V)) (hc : c ∈ (ω : V)) (hn : n ∈ (ω : V)) (hd : d ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement false).evalSet c) n) :
    decodedNaturalFormula (reindexCode.evalSet (naturalSquarePair r (naturalSquarePair d c))) =
      (formulaSubstitutionGraph membershipLanguageCode ∅ (reindexEnvironment r)) ‘
        ⟨⟨n, decodedNaturalFormula c⟩ₖ, d⟩ₖ :=
  decodedNaturalFormula_formulaTransform_substitution reindexArguments false (reindexEnvironment r)
    (reindexArguments_agree hr) hr hc hn hd hv

end ZFVP
