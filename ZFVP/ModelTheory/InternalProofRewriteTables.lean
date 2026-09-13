import ZFVP.ModelTheory.InternalProofRewriteEquations
import ZFVP.Syntax.FormulaSubstitutionDefinability
import ZFVP.Syntax.FormulaSubstitutionEquations

/-! Internal variable tables induced by the explicit natural-code rewrite program. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

attribute [local aesop 4 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def naturalProofRewriteTerm (s d c : V) : V :=
  decodedNaturalTerm (proofRewriteTerm.evalSet (naturalSquarePair s (naturalSquarePair d c)))

instance naturalProofRewriteTerm_definable : ℒₛₑₜ-function₃[V] naturalProofRewriteTerm := by
  unfold naturalProofRewriteTerm
  definability

noncomputable def proofRewriteVariableTable (s d tag : V) : V :=
  definableGraph ω (fun i ↦ naturalProofRewriteTerm s d (succ (naturalSquarePair tag i))) (by definability)

instance proofRewriteVariableTable_definable : ℒₛₑₜ-function₃[V] proofRewriteVariableTable := by
  have h : ℒₛₑₜ-relation₄ (fun B s d tag : V ↦ ∀ p, p ∈ B ↔
      ∃ i ∈ (ω : V), p = ⟨i, naturalProofRewriteTerm s d (succ (naturalSquarePair tag i))⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = proofRewriteVariableTable (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [proofRewriteVariableTable, mem_definableGraph_iff]

theorem proofRewriteVariableTable_value (s d tag : V) {i : V} (hi : i ∈ (ω : V)) :
    (proofRewriteVariableTable s d tag) ‘ i = naturalProofRewriteTerm s d (succ (naturalSquarePair tag i)) :=
  value_definableGraph _ _ _ hi

/-- The first two fields are unused by `formulaSubstitutionGraph`; the last two
    give its bound and free variable tables at the indexed binder depth. -/
noncomputable def proofRewriteEnvironment (s : V) : V :=
  definableGraph ω (fun d ↦ substitutionState 0 0
    (proofRewriteVariableTable s d 0) (proofRewriteVariableTable s d 1)) (by definability)

instance proofRewriteEnvironment_definable : ℒₛₑₜ-function₁[V] proofRewriteEnvironment := by
  have h : ℒₛₑₜ-relation (fun G s : V ↦ ∀ p, p ∈ G ↔ ∃ d ∈ (ω : V),
      p = ⟨d, substitutionState 0 0 (proofRewriteVariableTable s d 0) (proofRewriteVariableTable s d 1)⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = proofRewriteEnvironment (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [proofRewriteEnvironment, mem_definableGraph_iff]

@[simp] theorem proofRewriteEnvironment_bound (s : V) {d : V} (hd : d ∈ (ω : V)) :
    stateBound ((proofRewriteEnvironment s) ‘ d) = proofRewriteVariableTable s d 0 := by
  rw [proofRewriteEnvironment, value_definableGraph _ _ _ hd, stateBound_code]

@[simp] theorem proofRewriteEnvironment_free (s : V) {d : V} (hd : d ∈ (ω : V)) :
    stateFree ((proofRewriteEnvironment s) ‘ d) = proofRewriteVariableTable s d 1 := by
  rw [proofRewriteEnvironment, value_definableGraph _ _ _ hd, stateFree_code]

theorem naturalProofRewriteTerm_substitution (allowFree : Bool) (s d : V) {c n : V}
    (hc : c ∈ (ω : V)) (hn : n ∈ (ω : V))
    (hv : requirementFits ((termRequirement allowFree).evalSet c) n) :
    naturalProofRewriteTerm s d c =
      (termSubstitution membershipLanguageCode (naturalSyntaxFreeDomain allowFree) n
        (proofRewriteVariableTable s d 0) (proofRewriteVariableTable s d 1)) ‘ (decodedNaturalTerm c) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hc
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hn
  rw [← evalArithmetic_agreement, requirementFits_val, termRequirement_valid_iff] at hv
  rcases hv with ⟨i, hi, he⟩ | ⟨ha, i, he⟩
  · have hcode := congrArg internalArithmeticVal he
    simp only [internalArithmeticVal_succ, internalArithmeticVal_pair, internalArithmeticVal_zero] at hcode
    rw [hcode, decodedNaturalTerm_bound (internalArithmeticVal_mem i),
      termSubstitution_boundVar membershipLanguageCode_valid hn _ _ _ ((internalArithmetic_lt i v).mp hi),
      proofRewriteVariableTable_value _ _ _ (internalArithmeticVal_mem i)]
  · have hcode := congrArg internalArithmeticVal he
    simp only [internalArithmeticVal_succ, internalArithmeticVal_pair, internalArithmeticVal_one] at hcode
    have hi : internalArithmeticVal i ∈ naturalSyntaxFreeDomain (V := V) allowFree := by
      simpa only [naturalSyntaxFreeDomain, ha, ite_true] using internalArithmeticVal_mem i
    rw [hcode, decodedNaturalTerm_free (internalArithmeticVal_mem i),
      termSubstitution_freeVar membershipLanguageCode_valid hn _ _ _ hi,
      proofRewriteVariableTable_value _ _ _ (internalArithmeticVal_mem i)]

end ZFVP
