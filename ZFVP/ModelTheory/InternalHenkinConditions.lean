import ZFVP.ModelTheory.CodedProofBooleanInversion
import ZFVP.ModelTheory.StandardSentenceCoding
import ZFVP.Syntax.FormulaSubstitutionNegation

/-! Internally coded Henkin conditions and their decision and fresh-witness
extensions. Consistency means that the condition's negation has no finite proof. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsConsistentCodedFormula (T n φ : V) : Prop :=
  φ ∈ formulaSet membershipLanguageCode ∅ n ∧
    ¬∃ p, IsEqualityCodedSequentProof T p n {negateFormula membershipLanguageCode ∅ n φ}

noncomputable def henkinShiftFormula (n φ : V) : V :=
  renameMembershipFormula n (succ n) (successorIndices n) φ

instance consistentCodedFormula_definable : ℒₛₑₜ-relation₃[V] IsConsistentCodedFormula := by
  unfold IsConsistentCodedFormula
  definability

instance henkinShiftFormula_definable : ℒₛₑₜ-function₂[V] henkinShiftFormula := by
  unfold henkinShiftFormula
  exact Language.DefinableFunction₄.comp (by definability) (by definability)
    (by definability) (by definability)

theorem consistentCodedFormula_iff_standard (hω : Schmerl.HasStandardOmega V) (T n φ : V) :
    IsConsistentCodedFormula T n φ ↔ φ ∈ formulaSet membershipLanguageCode ∅ n ∧
      ¬StandardCodedProvable (T ∪ canonicalEqualityOpenCodes) n {negateFormula membershipLanguageCode ∅ n φ} :=
  and_congr Iff.rfl (not_congr (standardCodedProvable_iff_internal hω _ _ _).symm)

theorem henkinShiftFormula_valid {n φ : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) :
    henkinShiftFormula n φ ∈ formulaSet membershipLanguageCode ∅ (succ n) :=
  renameMembershipFormula_mem hn (ω_succ_closed hn) (successorIndices_function hn) hφ

theorem henkinShiftFormula_negate {n φ : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) :
    henkinShiftFormula n (negateFormula membershipLanguageCode ∅ n φ) =
      negateFormula membershipLanguageCode ∅ (succ n) (henkinShiftFormula n φ) :=
  renameMembershipFormula_negate hn (ω_succ_closed hn) (successorIndices_function hn) hφ

theorem shiftCodedSequent_singleton (n φ : V) :
    shiftCodedSequent n ({φ} : V) = ({henkinShiftFormula n φ} : V) := by
  ext ψ
  simp [shiftCodedSequent, mem_renameCodedSequent_iff, henkinShiftFormula]

namespace IsConsistentCodedFormula

theorem context {T n φ : V} (h : IsConsistentCodedFormula T n φ) : n ∈ (ω : V) :=
  formulaSet_context membershipLanguageCode_valid h.1

theorem conj_left (hω : Schmerl.HasStandardOmega V) {T n φ ψ : V}
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n)
    (h : IsConsistentCodedFormula T n (andCode φ ψ)) : IsConsistentCodedFormula T n φ := by
  refine ⟨hφ, ?_⟩
  rintro ⟨p, hp⟩
  exact h.2 (StandardCodedProvable.refute_conj_of_left hφ hψ (hp.to_standard hω)).to_internal

theorem conj_right (hω : Schmerl.HasStandardOmega V) {T n φ ψ : V}
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n)
    (h : IsConsistentCodedFormula T n (andCode φ ψ)) : IsConsistentCodedFormula T n ψ := by
  refine ⟨hψ, ?_⟩
  rintro ⟨p, hp⟩
  exact h.2 (StandardCodedProvable.refute_conj_of_right hφ hψ (hp.to_standard hω)).to_internal

theorem conj_provable (hω : Schmerl.HasStandardOmega V) {T n φ ψ : V}
    (h : IsConsistentCodedFormula T n φ) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n)
    (hp : StandardCodedProvable (T ∪ canonicalEqualityOpenCodes) n {ψ}) :
    IsConsistentCodedFormula T n (andCode φ ψ) := by
  have hn := h.context
  have hnf := negateFormula_mem membershipLanguageCode_valid h.1
  have hng := negateFormula_mem membershipLanguageCode_valid hψ
  refine ⟨(formulaSet_binary membershipLanguageCode_valid hn h.1 hψ).1, ?_⟩
  rintro ⟨q, hq⟩
  have hq' := hq.to_standard hω
  rw [negateFormula_and membershipLanguageCode_valid hn h.1 hψ] at hq'
  have hi := hq'.invert_or_singleton hnf hng
  have he : ({negateFormula membershipLanguageCode ∅ n φ, negateFormula membershipLanguageCode ∅ n ψ} : V) =
      insert (negateFormula membershipLanguageCode ∅ n ψ) ({negateFormula membershipLanguageCode ∅ n φ} : V) := by
    ext x; simp; tauto
  rw [he] at hi
  have hp' : StandardCodedProvable (T ∪ canonicalEqualityOpenCodes) n (insert ψ (∅ : V)) := by
    simpa only [SetTheory.insert_empty_eq] using hp
  have hc := hp'.cut hi (by simpa using isCodedSequent_singleton hn hnf) hψ
  have hc' : StandardCodedProvable (T ∪ canonicalEqualityOpenCodes) n
      {negateFormula membershipLanguageCode ∅ n φ} := by simpa using hc
  exact h.2 hc'.to_internal

theorem conj_swap (hω : Schmerl.HasStandardOmega V) {T n φ ψ : V}
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n)
    (h : IsConsistentCodedFormula T n (andCode φ ψ)) : IsConsistentCodedFormula T n (andCode ψ φ) := by
  have hn := h.context
  have hnf := negateFormula_mem membershipLanguageCode_valid hφ
  have hng := negateFormula_mem membershipLanguageCode_valid hψ
  refine ⟨(formulaSet_binary membershipLanguageCode_valid hn hψ hφ).1, ?_⟩
  rintro ⟨p, hp⟩
  have hp' := hp.to_standard hω
  rw [negateFormula_and membershipLanguageCode_valid hn hψ hφ] at hp'
  have hi := hp'.invert_or_singleton hng hnf
  have he : ({negateFormula membershipLanguageCode ∅ n ψ, negateFormula membershipLanguageCode ∅ n φ} : V) =
      insert (negateFormula membershipLanguageCode ∅ n φ) (insert (negateFormula membershipLanguageCode ∅ n ψ) (∅ : V)) := by
    ext x; simp; tauto
  rw [he] at hi
  have hc := hi.disj ((isCodedSequent_empty hn).insert (formulaSet_binary membershipLanguageCode_valid hn hnf hng).2) hnf hng
  have hr : StandardCodedProvable (T ∪ canonicalEqualityOpenCodes) n
      {negateFormula membershipLanguageCode ∅ n (andCode φ ψ)} := by
    rw [negateFormula_and membershipLanguageCode_valid hn hφ hψ]
    simpa only [SetTheory.insert_empty_eq] using hc
  exact h.2 hr.to_internal

theorem decide (hω : Schmerl.HasStandardOmega V) {T n φ ψ : V}
    (h : IsConsistentCodedFormula T n φ) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n) :
    IsConsistentCodedFormula T n (andCode φ ψ) ∨
      IsConsistentCodedFormula T n (andCode φ (negateFormula membershipLanguageCode ∅ n ψ)) := by
  classical
  by_cases hp : IsConsistentCodedFormula T n (andCode φ ψ)
  · exact Or.inl hp
  · right
    have hnψ := negateFormula_mem membershipLanguageCode_valid hψ
    refine ⟨(formulaSet_binary membershipLanguageCode_valid h.context h.1 hnψ).1, ?_⟩
    rintro ⟨q, hq⟩
    have hex : ∃ p, IsEqualityCodedSequentProof T p n
        {negateFormula membershipLanguageCode ∅ n (andCode φ ψ)} := by
      by_contra hh
      exact hp ⟨(formulaSet_binary membershipLanguageCode_valid h.context h.1 hψ).1, hh⟩
    obtain ⟨p, hp⟩ := hex
    exact h.2 (StandardCodedProvable.refute_of_refute_conj_both h.1 hψ
      (hp.to_standard hω) (hq.to_standard hω)).to_internal

theorem witness (hω : Schmerl.HasStandardOmega V) {T n φ ψ : V}
    (hn : n ∈ (ω : V)) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n))
    (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n)
    (h : IsConsistentCodedFormula T n (andCode (existsCode φ) ψ)) :
    IsConsistentCodedFormula T (succ n) (andCode φ (henkinShiftFormula n ψ)) := by
  have hshift := henkinShiftFormula_valid hn hψ
  have hnf := negateFormula_mem membershipLanguageCode_valid hφ
  have hng := negateFormula_mem membershipLanguageCode_valid hψ
  have hnshift := negateFormula_mem membershipLanguageCode_valid hshift
  have hex := (formulaSet_quantifiers membershipLanguageCode_valid hn hφ).2
  refine ⟨(formulaSet_binary membershipLanguageCode_valid (ω_succ_closed hn) hφ hshift).1, ?_⟩
  rintro ⟨p, hp⟩
  have hp' := hp.to_standard hω
  rw [negateFormula_and membershipLanguageCode_valid (ω_succ_closed hn) hφ hshift] at hp'
  have hi := hp'.invert_or_singleton hnf hnshift
  have hi' : StandardCodedProvable (T ∪ canonicalEqualityOpenCodes) (succ n)
      (insert (negateFormula membershipLanguageCode ∅ (succ n) φ)
        (shiftCodedSequent n ({negateFormula membershipLanguageCode ∅ n ψ} : V))) := by
    rw [shiftCodedSequent_singleton, henkinShiftFormula_negate hn hψ]
    exact hi
  have hv : IsCodedSequent n (insert (allCode (negateFormula membershipLanguageCode ∅ (succ n) φ))
      ({negateFormula membershipLanguageCode ∅ n ψ} : V)) :=
    (isCodedSequent_singleton hn hng).insert (formulaSet_quantifiers membershipLanguageCode_valid hn hnf).1
  have ha := hi'.all hv (by intro x hx; simpa using (mem_singleton_iff.mp hx) ▸ hng) hnf
  have hpairs : StandardCodedProvable (T ∪ canonicalEqualityOpenCodes) n
      (insert (negateFormula membershipLanguageCode ∅ n (existsCode φ))
        (insert (negateFormula membershipLanguageCode ∅ n ψ) (∅ : V))) := by
    rw [negateFormula_exists membershipLanguageCode_valid hn hφ, SetTheory.insert_empty_eq]
    exact ha
  have hne := negateFormula_mem membershipLanguageCode_valid hex
  have hdisj := hpairs.disj ((isCodedSequent_empty hn).insert
    (formulaSet_binary membershipLanguageCode_valid hn hne hng).2) hne hng
  have hres : StandardCodedProvable (T ∪ canonicalEqualityOpenCodes) n
      {negateFormula membershipLanguageCode ∅ n (andCode (existsCode φ) ψ)} := by
    rw [negateFormula_and membershipLanguageCode_valid hn hex hψ]
    simpa only [SetTheory.insert_empty_eq] using hdisj
  exact h.2 hres.to_internal

theorem of_satisfies {T D E n φ b : V} (hD : IsNonempty D)
    (hT : SatisfiesCodedOpenTheory membershipLanguageCode (binaryRelationStructureCode D E) T)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hb : b ∈ D ^ n)
    (hs : Satisfies membershipLanguageCode ∅ (binaryRelationStructureCode D E) ∅ n φ b) :
    IsConsistentCodedFormula T n φ := by
  refine ⟨hφ, ?_⟩
  rintro ⟨p, hp⟩
  obtain ⟨χ, hχ, hc⟩ := hp.coded_structure_sound hD hT b
    (by simpa only [binaryRelationStructureCode_domain] using hb)
  have he := mem_singleton_iff.mp hχ
  subst χ
  exact (satisfies_negateFormula membershipLanguageCode_valid hφ
    (by simpa only [binaryRelationStructureCode_domain] using hb)).mp hc hs

end IsConsistentCodedFormula

end ZFVP
