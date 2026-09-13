import ZFVP.Syntax.BoundedCodes
import ZFVP.SetTheory.FunctionUnion

/-! Atomic semantics for internal membership-language codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem membershipTerm_cases {n t : V} (hn : n ∈ (ω : V))
    (ht : t ∈ termSet membershipLanguageCode ∅ n) : ∃ i ∈ n, t = boundVarCode i := by
  rcases termSet_cases membershipLanguageCode_valid hn ∅ ht with h | ⟨x, hx, _⟩ | ⟨f, hf, _⟩
  · exact h
  · exact False.elim (not_mem_empty hx)
  · simp [membershipLanguageCode] at hf

theorem membershipTermEvaluation_eq {n : V} (hn : n ∈ (ω : V)) (M N b e f : V) :
    termEvaluation membershipLanguageCode ∅ n M b e =
      termEvaluation membershipLanguageCode ∅ n N b f := by
  apply functions_eq_of_domain_values (by simp)
  intro t ht
  simp only [domain_termEvaluation] at ht
  obtain ⟨i, hi, rfl⟩ := membershipTerm_cases hn ht
  rw [termEvaluation_boundVar membershipLanguageCode_valid hn ∅ M b e hi,
    termEvaluation_boundVar membershipLanguageCode_valid hn ∅ N b f hi]

theorem membershipEvaluatedArguments_eq {n : V} (hn : n ∈ (ω : V)) (M N b e f args : V) :
    evaluatedArguments membershipLanguageCode ∅ M e n b args =
      evaluatedArguments membershipLanguageCode ∅ N f n b args := by
  unfold evaluatedArguments evaluateWithFreeAssignment
  rw [membershipTermEvaluation_eq hn M N b e f]

theorem membershipAtomicHolds_iff {n A B b r args : V} (hn : n ∈ (ω : V))
    (hA : IsNonempty A) (hB : IsNonempty B) (hbA : b ∈ A ^ n) (hbB : b ∈ B ^ n)
    (ha : IsAtomicArguments membershipLanguageCode ∅ n r args) :
    AtomicHolds membershipLanguageCode ∅ (membershipStructureCode A) ∅ n b r args ↔
      AtomicHolds membershipLanguageCode ∅ (membershipStructureCode B) ∅ n b r args := by
  have he := membershipEvaluatedArguments_eq hn (membershipStructureCode A)
    (membershipStructureCode B) b ∅ ∅ args
  rcases ha with ⟨rfl, ha⟩ | ⟨s, hs, rfl, ha⟩
  · rw [atomicHolds_equality, atomicHolds_equality, he]
  · rw [atomicHolds_relation, atomicHolds_relation, and_iff_right hs, and_iff_right hs]
    have hs2 : s ∈ (2 : V) := by simpa [membershipLanguageCode] using hs
    have har : (relationArities (membershipLanguageCode : V)) ‘ s = (2 : V) := by
      simp only [membershipLanguageCode, relationArities_code]
      exact value_constantGraph _ _ hs2
    rw [har] at ha
    have haA : evaluatedArguments membershipLanguageCode ∅ (membershipStructureCode A) ∅ n b args ∈ A ^ (2 : V) := by
      simpa using evaluatedArguments_mem_function (membershipStructureCode_valid hA) hn
        (by simpa using hbA) (mem_function.intro (by simp) (by simp)) ha
    have haB : evaluatedArguments membershipLanguageCode ∅ (membershipStructureCode B) ∅ n b args ∈ B ^ (2 : V) := by
      simpa using evaluatedArguments_mem_function (membershipStructureCode_valid hB) hn
        (by simpa using hbB) (mem_function.intro (by simp) (by simp)) ha
    have htable (C : V) : (structureRelations (membershipStructureCode C)) ‘ s = membershipInterpretation C s := by
      simp only [membershipStructureCode, structureRelations_code, value_definableGraph _ _ _ hs2]
    rw [htable, htable]
    classical
    by_cases hs0 : s = 0
    · simp only [membershipInterpretation, hs0, ite_true, mem_equalityRelation_iff]
      rw [and_iff_right haA, and_iff_right haB, he]
    · simp only [membershipInterpretation, hs0, ite_false, mem_membershipTupleRelation_iff]
      rw [and_iff_right haA, and_iff_right haB, he]

theorem membershipGuard_evaluatedArguments {n i : V} (hn : n ∈ (ω : V)) (hi : i ∈ n)
    (M b : V) :
    evaluatedArguments membershipLanguageCode ∅ M ∅ (succ n) b (boundedGuardArguments i) =
      standardTuple ![b ‘ (0 : V), b ‘ (succ i)] := by
  unfold evaluatedArguments evaluateWithFreeAssignment boundedGuardArguments
  rw [compose_standardTuple]
  · congr 1
    funext j
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ Fin.elim0 k) j) j
    · exact termEvaluation_boundVar membershipLanguageCode_valid (ω_succ_closed hn) ∅ M b ∅
        (zero_mem_succ_natural hn)
    · exact termEvaluation_boundVar membershipLanguageCode_valid (ω_succ_closed hn) ∅ M b ∅
        (succ_mem_succ_of_natural_mem hn hi)
  · intro j
    simp only [domain_termEvaluation]
    have hc := (termSet_closed (membershipLanguageCode_valid (V := V)) (ω_succ_closed hn) ∅).1
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ Fin.elim0 k) j) j
    · exact hc _ (zero_mem_succ_natural hn)
    · exact hc _ (succ_mem_succ_of_natural_mem hn hi)

theorem membershipGuard_atomicHolds {n i A b x : V} (hn : n ∈ (ω : V)) (hi : i ∈ n)
    (hb : b ∈ A ^ n) (hx : x ∈ A) :
    AtomicHolds membershipLanguageCode ∅ (membershipStructureCode A) ∅ (succ n)
      (assignmentPrepend n b x) (relationToken (1 : V)) (boundedGuardArguments i) ↔ x ∈ b ‘ i := by
  have hr : (1 : V) ∈ relationSymbols membershipLanguageCode :=
    (membershipSymbol_valid (V := V) Language.Set.Rel.mem).1
  rw [atomicHolds_relation, and_iff_right hr,
    membershipStructureCode_membership, membershipGuard_evaluatedArguments hn hi,
    assignmentPrepend_zero hn, assignmentPrepend_succ hn hi]
  apply standardTuple_mem_membershipTupleRelation
  intro j
  refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ Fin.elim0 k) j) j
  · exact hx
  · exact function_value_mem hb hi

end ZFVP

