import ZFVP.ModelTheory.InternalNamedSeparationOmission
import ZFVP.ModelTheory.InternalNamedConjunction
import ZFVP.ModelTheory.InternalHenkinNameRenaming

/-! A unary query is compiled with its argument in one distinguished slot and
its fixed name parameters in a bounded context. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def namedUnaryQueryNegation (t : V) : V :=
  ⟨⟨Schmerl.definitionParameterCount t,
    negateFormula membershipLanguageCode ∅ (succ (Schmerl.definitionParameterCount t))
      (Schmerl.definitionFormula t)⟩ₖ, Schmerl.definitionTuple t⟩ₖ

@[simp] theorem namedUnaryQueryNegation_count (t : V) :
    Schmerl.definitionParameterCount (namedUnaryQueryNegation t) = Schmerl.definitionParameterCount t := by
  simp only [namedUnaryQueryNegation, Schmerl.definitionParameterCount_pair]

@[simp] theorem namedUnaryQueryNegation_tuple (t : V) :
    Schmerl.definitionTuple (namedUnaryQueryNegation t) = Schmerl.definitionTuple t := by
  simp only [namedUnaryQueryNegation, Schmerl.definitionTuple_pair]

theorem namedUnaryQueryNegation_valid {t : V} (ht : t ∈ (namedUnaryDefinitionQueries : V)) :
    namedUnaryQueryNegation t ∈ (namedUnaryDefinitionQueries : V) := by
  obtain ⟨hn, hφ, hb⟩ := namedUnaryDefinitionQueries_spec ht
  exact pair_mem_namedUnaryDefinitionQueries.mpr ⟨hn, negateFormula_mem membershipLanguageCode_valid hφ, hb⟩

@[simp] theorem namedUnaryQueryNegation_instance (t l : V) :
    namedUnaryQueryInstance (namedUnaryQueryNegation t) l =
      namedNegation membershipLanguageCode (namedUnaryQueryInstance t l) := by
  simp only [namedUnaryQueryInstance, namedUnaryQueryNegation, Schmerl.definitionParameterCount_pair,
    Schmerl.definitionFormula_pair, Schmerl.definitionTuple_pair, namedNegation_pair]

theorem queryTuple_mem_of_range {t n : V} (ht : t ∈ (namedUnaryDefinitionQueries : V))
    (hbound : range (Schmerl.definitionTuple t) ⊆ n) :
    Schmerl.definitionTuple t ∈ n ^ Schmerl.definitionParameterCount t :=
  namedTuple_mem_of_support (φ := truthCode) (namedUnaryDefinitionQueries_spec ht).2.2
    (by simpa only [namedFormulaSupport, kpair.π₂_kpair] using hbound)

noncomputable def namedQueryCodeInContext (n t : V) : V :=
  renameMembershipFormula (succ (Schmerl.definitionParameterCount t)) (succ n)
    (liftMembershipIndices (Schmerl.definitionParameterCount t) (Schmerl.definitionTuple t))
    (Schmerl.definitionFormula t)

theorem namedQueryCodeInContext_mem {t n : V} (ht : t ∈ (namedUnaryDefinitionQueries : V))
    (hn : n ∈ (ω : V)) (hbound : range (Schmerl.definitionTuple t) ⊆ n) :
    namedQueryCodeInContext n t ∈ formulaSet membershipLanguageCode ∅ (succ n) := by
  obtain ⟨hq, hφ, _⟩ := namedUnaryDefinitionQueries_spec ht
  exact renameMembershipFormula_mem (ω_succ_closed hq) (ω_succ_closed hn)
    (liftMembershipIndices_function hq hn (queryTuple_mem_of_range ht hbound)) hφ

theorem namedQueryCodeInContext_satisfies {M j f t n x : V}
    (hM : IsStructureCode membershipLanguageCode M) (hj : j ∈ (ω : V) ^ structureDomain M)
    (hf : SourceNaming M j f) (ht : t ∈ (namedUnaryDefinitionQueries : V))
    (hn : n ∈ (ω : V)) (hbound : range (Schmerl.definitionTuple t) ⊆ n)
    (hx : x ∈ structureDomain M) :
    Satisfies membershipLanguageCode ∅ M ∅ (succ n) (namedQueryCodeInContext n t)
      (assignmentPrepend n (f ↾ n) x) ↔
      NamedHolds membershipLanguageCode M f (namedUnaryQueryInstance t (j ‘ x)) := by
  obtain ⟨hq, hφ, _⟩ := namedUnaryDefinitionQueries_spec ht
  have hb := queryTuple_mem_of_range ht hbound
  have hfn := function_restrict_mem hf.1 (IsTransitive.ω.transitive n hn)
  rw [namedUnaryQueryInstance_holds hf.1 ht (function_value_mem hj hx), hf.2 x hx]
  change Satisfies membershipLanguageCode ∅ M ∅ (succ n)
    (renameMembershipFormula _ _ _ _) (assignmentPrepend n (f ↾ n) x) ↔ _
  rw [codedMembershipSatisfies_rename hM (ω_succ_closed hq) (ω_succ_closed hn)
    (liftMembershipIndices_function hq hn hb) hφ (assignmentPrepend_mem_function hn hfn hx),
    liftMembershipIndices_compose_prepend hq hn hb hfn hx, graph_compose_restrict hb]
  rfl

theorem exists_internal_namedQueryConjunction {A t : V} (hA : IsInternallyFinite A)
    (hsub : A ⊆ namedFormulaSet membershipLanguageCode (ω : V))
    (ht : t ∈ (namedUnaryDefinitionQueries : V)) :
    ∃ n ∈ (ω : V), namedTheorySupport A ⊆ n ∧ range (Schmerl.definitionTuple t) ⊆ n ∧
      ∃ χ ∈ formulaSet membershipLanguageCode ∅ n,
        ∀ M, IsStructureCode membershipLanguageCode M →
          ∀ f ∈ structureDomain M ^ (ω : V),
            ((∀ p ∈ A, NamedHolds membershipLanguageCode M f p) ↔
              Satisfies membershipLanguageCode ∅ M ∅ n χ (f ↾ n)) := by
  obtain ⟨hq, _, hb⟩ := namedUnaryDefinitionQueries_spec ht
  let d : V := ⟨⟨Schmerl.definitionParameterCount t, truthCode⟩ₖ, Schmerl.definitionTuple t⟩ₖ
  have hd : d ∈ namedFormulaSet membershipLanguageCode (ω : V) :=
    (pair_mem_namedFormulaSet_iff membershipLanguageCode_valid).mpr
      ⟨(formulaSet_constants membershipLanguageCode_valid hq ∅).1, hb⟩
  have hB : insert d A ⊆ namedFormulaSet membershipLanguageCode (ω : V) := by
    intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · exact hd
    · exact hsub p hp
  obtain ⟨n, hn, hsupport, χ, hχ, heq⟩ :=
    exists_internal_namedConjunction (internallyFinite_insert hA d) hB
  refine ⟨n, hn, ?_, ?_, χ, hχ, ?_⟩
  · intro i hi
    obtain ⟨p, hp, hi⟩ := (mem_namedTheorySupport A i).mp hi
    exact hsupport i ((mem_namedTheorySupport (insert d A) i).mpr ⟨p, mem_insert.mpr (Or.inr hp), hi⟩)
  · intro i hi
    exact hsupport i ((mem_namedTheorySupport (insert d A) i).mpr ⟨d, by simp,
      by simpa only [d, namedFormulaSupport, kpair.π₂_kpair] using hi⟩)
  · intro M hM f hf
    have hdH : NamedHolds membershipLanguageCode M f d := by
      rw [namedHolds_pair]
      exact (satisfies_truth membershipLanguageCode_valid hq).mpr (compose_function hb hf)
    rw [← heq M hM f hf]
    constructor
    · intro ha p hp
      rcases mem_insert.mp hp with rfl | hp
      · exact hdH
      · exact ha p hp
    · intro ha p hp
      exact ha p (mem_insert.mpr (Or.inr hp))

end ZFVP
