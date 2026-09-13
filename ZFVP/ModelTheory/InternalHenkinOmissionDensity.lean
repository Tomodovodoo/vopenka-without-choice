import ZFVP.ModelTheory.InternalHenkinTypeProjection

/-! Omission density for an actual internally coded unary type. Nonprincipality
has its usual syntactic meaning: no consistent unary formula implies every
member of the type. Density is proved from that definition. -/

set_option autoImplicit false

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsNonprincipalCodedType (T P : V) : Prop :=
  P ⊆ formulaSet (membershipLanguageCode : V) ∅ 1 ∧
    ¬∃ θ : V, IsConsistentCodedFormula T 1 θ ∧ ∀ ψ ∈ P, CodedFormulaImplies T 1 θ ψ

instance nonprincipalCodedType_definable : ℒₛₑₜ-relation[V] IsNonprincipalCodedType := by
  unfold IsNonprincipalCodedType
  definability

theorem CodedFormulaImplies.of_inconsistent_neg_conj (hω : Schmerl.HasStandardOmega V) {T n φ ψ : V}
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n)
    (h : ¬IsConsistentCodedFormula T n (andCode φ (negateFormula membershipLanguageCode ∅ n ψ))) :
    CodedFormulaImplies T n φ ψ := by
  classical
  have hn := formulaSet_context membershipLanguageCode_valid hφ
  have hnf := negateFormula_mem membershipLanguageCode_valid hφ
  have hng := negateFormula_mem membershipLanguageCode_valid hψ
  have hv := (formulaSet_binary membershipLanguageCode_valid hn hφ hng).1
  obtain ⟨p, hp⟩ : ∃ p, IsEqualityCodedSequentProof T p n
      {negateFormula membershipLanguageCode ∅ n (andCode φ (negateFormula membershipLanguageCode ∅ n ψ))} := by
    by_contra hh
    exact h ⟨hv, hh⟩
  have hp' := hp.to_standard hω
  rw [negateFormula_and membershipLanguageCode_valid hn hφ hng,
    negateFormula_involutive membershipLanguageCode_valid hψ] at hp'
  have hi := hp'.invert_or_singleton hnf hψ
  have he : ({negateFormula membershipLanguageCode ∅ n φ, ψ} : V) =
      ({ψ, negateFormula membershipLanguageCode ∅ n φ} : V) := by ext x; simp; tauto
  rw [he] at hi
  exact ⟨hφ, hψ, hi.to_internal⟩

theorem IsNonprincipalCodedType.omission_dense (hω : Schmerl.HasStandardOmega V) {T P n i χ : V}
    (hP : IsNonprincipalCodedType T P) (hχ : IsConsistentCodedFormula T n χ) (hi : i ∈ n) :
    ∃ ψ ∈ P, IsConsistentCodedFormula T n
      (andCode χ (negateFormula membershipLanguageCode ∅ n (unaryCodedInstance n i ψ))) := by
  classical
  by_contra hnone
  apply hP.2
  apply exists_unary_principal_of_context hω hP.1 hχ hi
  intro ψ hψ
  apply CodedFormulaImplies.of_inconsistent_neg_conj hω hχ.1
    (unaryCodedInstance_valid hχ.context hi (hP.1 ψ hψ))
  intro hc
  exact hnone ⟨ψ, hψ, hc⟩

noncomputable def henkinOmissionChoices (T P n i χ : V) : V :=
  {ψ ∈ P ; IsConsistentCodedFormula T n
    (andCode χ (negateFormula membershipLanguageCode ∅ n (unaryCodedInstance n i ψ)))}

theorem IsNonprincipalCodedType.omissionChoices_nonempty (hω : Schmerl.HasStandardOmega V) {T P n i χ : V}
    (hP : IsNonprincipalCodedType T P) (hχ : IsConsistentCodedFormula T n χ) (hi : i ∈ n) :
    IsNonempty (henkinOmissionChoices T P n i χ) := by
  obtain ⟨ψ, hψ, hc⟩ := hP.omission_dense hω hχ hi
  exact ⟨⟨ψ, mem_sep_iff.mpr ⟨hψ, hc⟩⟩⟩

theorem IsNonprincipalCodedType.omission_condition (hω : Schmerl.HasStandardOmega V) {T P n i χ : V}
    (hP : IsNonprincipalCodedType T P) (hχ : ⟨n, χ⟩ₖ ∈ henkinConditions T) (hi : i ∈ n) :
    ∃ ψ ∈ P, ∃ χ' : V,
      χ' = andCode χ (negateFormula membershipLanguageCode ∅ n (unaryCodedInstance n i ψ)) ∧
      ⟨n, χ'⟩ₖ ∈ henkinConditions T ∧ CodedFormulaImplies T n χ' χ := by
  obtain ⟨hzero, hc⟩ := (pair_mem_henkinConditions_iff _ _ _).mp hχ
  obtain ⟨ψ, hψ, he⟩ := hP.omission_dense hω hc hi
  refine ⟨ψ, hψ, _, rfl, (pair_mem_henkinConditions_iff _ _ _).mpr ⟨hzero, he⟩, ?_⟩
  exact CodedFormulaImplies.conj_left T hc.1
    (negateFormula_mem membershipLanguageCode_valid (unaryCodedInstance_valid hc.context hi (hP.1 ψ hψ)))

end ZFVP
