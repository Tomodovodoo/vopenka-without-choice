import ZFVP.ModelTheory.InternalHenkinStages
import ZFVP.Syntax.MembershipRenamingConstructors

/-! Syntactic implications between Henkin conditions and preservation of the
chosen existential literal by its fresh witness. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def CodedFormulaImplies (T n φ ψ : V) : Prop :=
  φ ∈ formulaSet membershipLanguageCode ∅ n ∧ ψ ∈ formulaSet membershipLanguageCode ∅ n ∧
    ∃ p, IsEqualityCodedSequentProof T p n {ψ, negateFormula membershipLanguageCode ∅ n φ}

instance codedFormulaImplies_definable : ℒₛₑₜ-relation₄[V] CodedFormulaImplies := by
  unfold CodedFormulaImplies
  definability

theorem codedFormulaImplies_iff_standard (hω : Schmerl.HasStandardOmega V) (T n φ ψ : V) :
    CodedFormulaImplies T n φ ψ ↔
      φ ∈ formulaSet membershipLanguageCode ∅ n ∧ ψ ∈ formulaSet membershipLanguageCode ∅ n ∧
        StandardCodedProvable (T ∪ canonicalEqualityOpenCodes) n {ψ, negateFormula membershipLanguageCode ∅ n φ} := by
  exact and_congr Iff.rfl (and_congr Iff.rfl (standardCodedProvable_iff_internal hω _ _ _).symm)

namespace CodedFormulaImplies

theorem refl (T : V) {n φ : V} (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) :
    CodedFormulaImplies T n φ φ :=
  ⟨hφ, hφ, (StandardCodedProvable.identity _ (formulaSet_context membershipLanguageCode_valid hφ) hφ).to_internal⟩

theorem trans (hω : Schmerl.HasStandardOmega V) {T n φ ψ χ : V}
    (h : CodedFormulaImplies T n φ ψ) (g : CodedFormulaImplies T n ψ χ) :
    CodedFormulaImplies T n φ χ := by
  have hn := formulaSet_context membershipLanguageCode_valid h.1
  have hp := ((codedFormulaImplies_iff_standard hω _ _ _ _).mp h).2.2
  have hq := ((codedFormulaImplies_iff_standard hω _ _ _ _).mp g).2.2
  have he : ({χ, negateFormula membershipLanguageCode ∅ n ψ} : V) =
      insert (negateFormula membershipLanguageCode ∅ n ψ) ({χ} : V) := by ext x; simp; tauto
  rw [he] at hq
  have he' : ({negateFormula membershipLanguageCode ∅ n φ} : V) ∪ {χ} =
      ({χ, negateFormula membershipLanguageCode ∅ n φ} : V) := by ext x; simp; tauto
  have hv := (isCodedSequent_singleton hn (negateFormula_mem membershipLanguageCode_valid h.1)).insert g.2.1
  have hc := hp.cut hq (he'.symm ▸ hv) h.2.1
  rw [he'] at hc
  exact ⟨h.1, g.2.1, hc.to_internal⟩

theorem conj_left (T : V) {n φ ψ : V}
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n) :
    CodedFormulaImplies T n (andCode φ ψ) φ := by
  have hn := formulaSet_context membershipLanguageCode_valid hφ
  have ha := (formulaSet_binary membershipLanguageCode_valid hn hφ hψ).1
  have hp := StandardCodedProvable.identity (T ∪ canonicalEqualityOpenCodes) hn ha
  have hc := hp.invert_and_left hφ hψ (isCodedSequent_singleton hn (negateFormula_mem membershipLanguageCode_valid ha))
  exact ⟨ha, hφ, hc.to_internal⟩

theorem conj_right (T : V) {n φ ψ : V}
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n) :
    CodedFormulaImplies T n (andCode φ ψ) ψ := by
  have hn := formulaSet_context membershipLanguageCode_valid hφ
  have ha := (formulaSet_binary membershipLanguageCode_valid hn hφ hψ).1
  have hp := StandardCodedProvable.identity (T ∪ canonicalEqualityOpenCodes) hn ha
  have hc := hp.invert_and_right hφ hψ (isCodedSequent_singleton hn (negateFormula_mem membershipLanguageCode_valid ha))
  exact ⟨ha, hψ, hc.to_internal⟩

theorem consistent (hω : Schmerl.HasStandardOmega V) {T n φ ψ : V}
    (h : CodedFormulaImplies T n φ ψ) (hc : IsConsistentCodedFormula T n φ) :
    IsConsistentCodedFormula T n ψ := by
  refine ⟨h.2.1, ?_⟩
  rintro ⟨p, hp⟩
  have hi := ((codedFormulaImplies_iff_standard hω _ _ _ _).mp h).2.2
  have hr : StandardCodedProvable (T ∪ canonicalEqualityOpenCodes) n
      (insert (negateFormula membershipLanguageCode ∅ n ψ) (∅ : V)) := by
    simpa only [SetTheory.insert_empty_eq] using hp.to_standard hω
  have hx := hi.cut hr (by simpa using isCodedSequent_singleton hc.context (negateFormula_mem membershipLanguageCode_valid hc.1)) h.2.1
  apply hc.2
  exact (by simpa using hx : StandardCodedProvable (T ∪ canonicalEqualityOpenCodes) n
    {negateFormula membershipLanguageCode ∅ n φ}).to_internal

theorem rename (hω : Schmerl.HasStandardOmega V) {T n m r φ ψ : V}
    (h : CodedFormulaImplies T n φ ψ) (hm : m ∈ (ω : V)) (hr : r ∈ m ^ n) :
    CodedFormulaImplies T m (renameMembershipFormula n m r φ) (renameMembershipFormula n m r ψ) := by
  have hn := formulaSet_context membershipLanguageCode_valid h.1
  have hφ := renameMembershipFormula_mem hn hm hr h.1
  have hψ := renameMembershipFormula_mem hn hm hr h.2.1
  have hp := ((codedFormulaImplies_iff_standard hω _ _ _ _).mp h).2.2
  have he : renameCodedSequent n m r ({ψ, negateFormula membershipLanguageCode ∅ n φ} : V) =
      ({renameMembershipFormula n m r ψ, negateFormula membershipLanguageCode ∅ m
        (renameMembershipFormula n m r φ)} : V) := by
    ext x
    simp only [mem_renameCodedSequent_iff, mem_insert, mem_singleton_iff]
    constructor
    · rintro ⟨χ, (rfl | rfl), hx⟩
      · exact Or.inl hx
      · exact Or.inr (hx.trans (renameMembershipFormula_negate hn hm hr h.1))
    · rintro (hx | hx)
      · exact ⟨ψ, Or.inl rfl, hx⟩
      · exact ⟨_, Or.inr rfl, hx.trans (renameMembershipFormula_negate hn hm hr h.1).symm⟩
  have hv := (isCodedSequent_singleton hm (negateFormula_mem membershipLanguageCode_valid hφ)).insert hψ
  have hc := hp.rename (he.symm ▸ hv) hr
  rw [he] at hc
  exact ⟨hφ, hψ, hc.to_internal⟩

end CodedFormulaImplies

theorem liftSuccessorIndices_instantiate_zero {n : V} (hn : n ∈ (ω : V)) :
    compose (liftMembershipIndices n (successorIndices n))
      (assignmentPrepend (succ n) (SetTheory.identity (succ n)) (0 : V)) = SetTheory.identity (succ n) := by
  have hL := liftMembershipIndices_function hn (ω_succ_closed hn) (successorIndices_function hn)
  have hR := assignmentPrepend_mem_function (ω_succ_closed hn) (identity_mem_function (succ n)) (zero_mem_succ_natural hn)
  apply function_eq_of_values (compose_function hL hR) (identity_mem_function _)
  intro i hi
  rw [value_compose_of_mem_function hL hR hi, identity_value hi]
  rcases internalBoundIndex_cases hn hi with rfl | ⟨j, hj, rfl⟩
  · rw [liftMembershipIndices_zero hn, assignmentPrepend_zero (ω_succ_closed hn)]
  · rw [liftMembershipIndices_succ hn hj,
      show (successorIndices n) ‘ j = succ j from value_definableGraph _ _ _ hj,
      assignmentPrepend_succ (ω_succ_closed hn) (succ_mem_succ_of_natural_mem hn hj),
      identity_value (succ_mem_succ_of_natural_mem hn hj)]

theorem instantiate_shifted_exists_body {n φ : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) :
    instantiateMembershipFormula (succ n) 0
      (renameMembershipFormula (succ n) (succ (succ n)) (liftMembershipIndices n (successorIndices n)) φ) = φ := by
  rw [instantiateMembershipFormula,
    renameMembershipFormula_compose (ω_succ_closed hn) (ω_succ_closed (ω_succ_closed hn)) (ω_succ_closed hn)
      (liftMembershipIndices_function hn (ω_succ_closed hn) (successorIndices_function hn))
      (assignmentPrepend_mem_function (ω_succ_closed hn) (identity_mem_function (succ n)) (zero_mem_succ_natural hn)) hφ,
    liftSuccessorIndices_instantiate_zero hn, renameMembershipFormula_identity (ω_succ_closed hn) hφ]

theorem CodedFormulaImplies.witness_exists (T : V) {n φ : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) :
    CodedFormulaImplies T (succ n) φ (henkinShiftFormula n (existsCode φ)) := by
  have hρ := liftMembershipIndices_function hn (ω_succ_closed hn) (successorIndices_function hn)
  let χ := renameMembershipFormula (succ n) (succ (succ n)) (liftMembershipIndices n (successorIndices n)) φ
  have hχ : χ ∈ formulaSet membershipLanguageCode ∅ (succ (succ n)) :=
    renameMembershipFormula_mem (ω_succ_closed hn) (ω_succ_closed (ω_succ_closed hn)) hρ hφ
  have he : henkinShiftFormula n (existsCode φ) = existsCode χ :=
    renameMembershipFormula_exists hn (ω_succ_closed hn) (successorIndices_function hn) hφ
  have hx := (formulaSet_quantifiers membershipLanguageCode_valid (ω_succ_closed hn) hχ).2
  have hp : StandardCodedProvable (T ∪ canonicalEqualityOpenCodes) (succ n)
      (insert (instantiateMembershipFormula (succ n) 0 χ)
        ({negateFormula membershipLanguageCode ∅ (succ n) φ} : V)) := by
    rw [show instantiateMembershipFormula (succ n) 0 χ = φ from instantiate_shifted_exists_body hn hφ]
    exact StandardCodedProvable.identity _ (ω_succ_closed hn) hφ
  have hproof := hp.exists ((isCodedSequent_singleton (ω_succ_closed hn)
    (negateFormula_mem membershipLanguageCode_valid hφ)).insert hx) (zero_mem_succ_natural hn) hχ
  rw [he]
  exact ⟨hφ, hx, hproof.to_internal⟩

end ZFVP
