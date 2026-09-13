import ZFVP.ModelTheory.InternalHenkinConditions
import ZFVP.SetTheory.NaturalAddition

/-! Positive Henkin contexts may be enlarged by any internal finite amount.
The iterated extension is an actual definable set-valued operation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace StandardCodedProvable

theorem nonempty_context (T : V) {n : V} (hn : n ∈ (ω : V)) (hzero : (0 : V) ∈ n) :
    StandardCodedProvable T n {existsCode truthCode} := by
  have ht := (formulaSet_constants (membershipLanguageCode_valid (V := V)) hn ∅).1
  have ht' := (formulaSet_constants (membershipLanguageCode_valid (V := V)) (ω_succ_closed hn) ∅).1
  have hp : StandardCodedProvable T n (insert (instantiateMembershipFormula n 0 truthCode) (∅ : V)) := by
    rw [instantiateMembershipFormula, renameMembershipFormula_truth (ω_succ_closed hn), SetTheory.insert_empty_eq]
    exact verum T hn
  have he := hp.exists ((isCodedSequent_empty hn).insert (formulaSet_quantifiers membershipLanguageCode_valid hn ht').2)
    hzero ht'
  simpa only [SetTheory.insert_empty_eq] using he

theorem refutation_of_falsity {T n : V} (h : StandardCodedProvable T n ({falsityCode} : V)) :
    StandardCodedProvable T n (∅ : V) := by
  have hn := h.valid.1
  have ht := (formulaSet_constants (membershipLanguageCode_valid (V := V)) hn ∅).1
  have hp : StandardCodedProvable T n (insert truthCode (∅ : V)) := by
    simpa only [SetTheory.insert_empty_eq] using verum T hn
  have hq : StandardCodedProvable T n (insert (negateFormula membershipLanguageCode ∅ n truthCode) (∅ : V)) := by
    rw [negateFormula_truth membershipLanguageCode_valid hn, SetTheory.insert_empty_eq]
    exact h
  simpa using hp.cut hq (by simpa using isCodedSequent_empty hn) ht

end StandardCodedProvable

theorem EqualityCodedSequentConsistent.initialCondition (hω : Schmerl.HasStandardOmega V)
    {T : V} (hT : EqualityCodedSequentConsistent T) : IsConsistentCodedFormula T 1 truthCode := by
  refine ⟨(formulaSet_constants membershipLanguageCode_valid (by simp) ∅).1, ?_⟩
  rintro ⟨p, hp⟩
  have hf := hp.to_standard hω
  rw [negateFormula_truth membershipLanguageCode_valid (by simp)] at hf
  have hne : StandardCodedProvable (T ∪ canonicalEqualityOpenCodes) 0
      {encodeMembershipFormula (∃¹ (⊤ : SetTheorySemisentence 1))} := by
    apply StandardCodedProvable.axiom (by simp) (encodeSentence_valid _)
    apply mem_union_iff.mpr
    exact Or.inr (by simp [canonicalEqualityOpenCodes, nonemptyDomainSentence])
  exact hT (hf.refutation_of_falsity.refutation_zero hne).to_internal

theorem IsConsistentCodedFormula.shift (hω : Schmerl.HasStandardOmega V) {T n φ : V}
    (h : IsConsistentCodedFormula T n φ) (hzero : (0 : V) ∈ n) :
    IsConsistentCodedFormula T (succ n) (henkinShiftFormula n φ) := by
  have ht := (formulaSet_constants (membershipLanguageCode_valid (V := V)) (ω_succ_closed h.context) ∅).1
  have hex := (formulaSet_quantifiers membershipLanguageCode_valid h.context ht).2
  have hcon := h.conj_provable hω hex (StandardCodedProvable.nonempty_context _ h.context hzero)
  have hcon' := hcon.conj_swap hω h.1 hex
  have hstep := hcon'.witness hω h.context ht h.1
  exact hstep.conj_right hω ht (henkinShiftFormula_valid h.context h.1)

noncomputable def henkinShiftCode (p : V) : V :=
  ⟨succ (kpair.π₁ p), henkinShiftFormula (kpair.π₁ p) (kpair.π₂ p)⟩ₖ

instance henkinShiftCode_definable : ℒₛₑₜ-function₁[V] henkinShiftCode := by
  unfold henkinShiftCode
  definability

noncomputable def henkinLiftCode (p k : V) : V := naturalIteration henkinShiftCode (by definability) p k

theorem naturalIteration_definable₂ (F : V → V) (hF : ℒₛₑₜ-function₁ F) :
    ℒₛₑₜ-function₂ (naturalIteration F hF) := by
  have hstep : ℒₛₑₜ-function₂ (naturalIterationStep F) := by
    have he : ℒₛₑₜ-relation₃ (fun y a g : V ↦
        (domain g = 0 ∧ y = a) ∨ (domain g ≠ 0 ∧ y = F (g ‘ (⋃ˢ domain g)))) := by definability
    apply Language.Definable.of_iff he
    intro v
    change v 0 = naturalIterationStep F (v 1) (v 2) ↔ _
    unfold naturalIterationStep
    split <;> simp_all
  have he : ℒₛₑₜ-relation₃ (fun y a k : V ↦
      (∃ g, IsAttempt (naturalIterationStep F a) k g ∧ y = naturalIterationStep F a g) ∨
      (¬IsOrdinal k ∧ y = ∅)) := by
    unfold IsAttempt
    definability
  apply Language.Definable.of_iff he
  intro v
  exact transfiniteRec_eq_iff (naturalIterationStep F (v 1)) (by definability) (v 2) (v 0)

instance henkinLiftCode_definable : ℒₛₑₜ-function₂[V] henkinLiftCode :=
  naturalIteration_definable₂ henkinShiftCode (by definability)

theorem henkinLiftCode_zero (p : V) : henkinLiftCode p 0 = p :=
  naturalIteration_zero _ _ _

theorem henkinLiftCode_succ (p : V) {k : V} (hk : k ∈ (ω : V)) :
    henkinLiftCode p (succ k) = henkinShiftCode (henkinLiftCode p k) :=
  naturalIteration_succ _ _ _ hk

theorem henkinLiftCode_context {n k : V} (hn : n ∈ (ω : V)) (hk : k ∈ (ω : V)) (φ : V) :
    kpair.π₁ (henkinLiftCode ⟨n, φ⟩ₖ k) = ordinalAdd n k := by
  apply naturalNumber_induction (fun k ↦ kpair.π₁ (henkinLiftCode ⟨n, φ⟩ₖ k) = ordinalAdd n k)
    (by definability) ?_ ?_ k hk
  · rw [henkinLiftCode_zero, kpair.π₁_kpair, zero_def, ordinalAdd_zero]
  · intro k hk ih
    let := IsOrdinal.of_mem hn
    let := IsOrdinal.of_mem hk
    rw [henkinLiftCode_succ _ hk, henkinShiftCode, kpair.π₁_kpair, ih, ordinalAdd_succ]

theorem henkinLiftCode_consistent (hω : Schmerl.HasStandardOmega V) {T n φ k : V}
    (h : IsConsistentCodedFormula T n φ) (hzero : (0 : V) ∈ n) (hk : k ∈ (ω : V)) :
    (0 : V) ∈ kpair.π₁ (henkinLiftCode ⟨n, φ⟩ₖ k) ∧
      IsConsistentCodedFormula T (kpair.π₁ (henkinLiftCode ⟨n, φ⟩ₖ k))
        (kpair.π₂ (henkinLiftCode ⟨n, φ⟩ₖ k)) := by
  apply naturalNumber_induction (fun k ↦
    (0 : V) ∈ kpair.π₁ (henkinLiftCode ⟨n, φ⟩ₖ k) ∧
      IsConsistentCodedFormula T (kpair.π₁ (henkinLiftCode ⟨n, φ⟩ₖ k))
        (kpair.π₂ (henkinLiftCode ⟨n, φ⟩ₖ k))) (by definability) ?_ ?_ k hk
  · simpa only [henkinLiftCode_zero, kpair.π₁_kpair, kpair.π₂_kpair] using And.intro hzero h
  · intro k hk ih
    rw [henkinLiftCode_succ _ hk, henkinShiftCode, kpair.π₁_kpair, kpair.π₂_kpair]
    exact ⟨zero_mem_succ_natural ih.2.context, ih.2.shift hω ih.1⟩

end ZFVP
