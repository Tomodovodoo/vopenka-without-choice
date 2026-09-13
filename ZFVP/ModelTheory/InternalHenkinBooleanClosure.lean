import ZFVP.ModelTheory.InternalHenkinAcceptance

/-! Boolean truth and invariance under finite context extension for the
completed internal Henkin diagram. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsCompleteHenkinSequence (T s : V) : Prop :=
  IsCoherentHenkinSequence T s ∧ ∀ n φ : V, φ ∈ formulaSet membershipLanguageCode ∅ n →
    HenkinAccepted T s ⟨n, φ⟩ₖ ∨ HenkinAccepted T s ⟨n, negateFormula membershipLanguageCode ∅ n φ⟩ₖ

instance completeHenkinSequence_definable : ℒₛₑₜ-relation[V] IsCompleteHenkinSequence := by
  unfold IsCompleteHenkinSequence
  definability

theorem henkinStages_complete (hω : Schmerl.HasStandardOmega V) {T e : V}
    (hT : EqualityCodedSequentConsistent T)
    (he : e ∈ (formulaFamily (membershipLanguageCode : V) ∅) ^ (ω : V))
    (hrange : range e = formulaFamily (membershipLanguageCode : V) ∅) :
    IsCompleteHenkinSequence T (henkinStages T e) :=
  ⟨henkinStages_coherent hω hT he, fun _ _ hφ ↦ henkinStages_decides hω hT he hrange hφ⟩

theorem IsCompleteHenkinSequence.negate_iff (hω : Schmerl.HasStandardOmega V) {T s n φ : V}
    (hs : IsCompleteHenkinSequence T s) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) :
    HenkinAccepted T s ⟨n, negateFormula membershipLanguageCode ∅ n φ⟩ₖ ↔ ¬HenkinAccepted T s ⟨n, φ⟩ₖ :=
  ⟨fun hn hp ↦ hp.not_negate hω hs.1 hn, fun hp ↦ (hs.2 n φ hφ).resolve_left hp⟩

theorem IsCompleteHenkinSequence.lift_iff (hω : Schmerl.HasStandardOmega V) {T s n φ k : V}
    (hs : IsCompleteHenkinSequence T s) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n)
    (hk : k ∈ (ω : V)) :
    HenkinAccepted T s (henkinLiftCode ⟨n, φ⟩ₖ k) ↔ HenkinAccepted T s ⟨n, φ⟩ₖ := by
  constructor
  · exact fun h ↦ h.of_refines hω (HenkinRefines.lift T ((mem_formulaSet_iff _ _ _ _).mp hφ) hk)
  · intro hp
    by_contra hn
    have hv := henkinLiftCode_valid hφ hk
    have hpairs := henkinLiftCode_pair n φ hk
    have hnot : ¬HenkinAccepted T s
        ⟨kpair.π₁ (henkinLiftCode ⟨n, φ⟩ₖ k), kpair.π₂ (henkinLiftCode ⟨n, φ⟩ₖ k)⟩ₖ := by
      simpa only [← hpairs] using hn
    have hneg := (hs.negate_iff hω hv).mpr hnot
    rw [← henkinLiftCode_negate hφ hk] at hneg
    have hf := hneg.of_refines hω (HenkinRefines.lift T ((mem_formulaSet_iff _ _ _ _).mp
      (negateFormula_mem membershipLanguageCode_valid hφ)) hk)
    exact hp.not_negate hω hs.1 hf

theorem CodedFormulaImplies.conj (hω : Schmerl.HasStandardOmega V) {T n φ ψ χ : V}
    (hp : CodedFormulaImplies T n φ ψ) (hq : CodedFormulaImplies T n φ χ) :
    CodedFormulaImplies T n φ (andCode ψ χ) := by
  have hn := formulaSet_context membershipLanguageCode_valid hp.1
  have hψχ := (formulaSet_binary membershipLanguageCode_valid hn hp.2.1 hq.2.1).1
  have hp' := ((codedFormulaImplies_iff_standard hω _ _ _ _).mp hp).2.2
  have hq' := ((codedFormulaImplies_iff_standard hω _ _ _ _).mp hq).2.2
  have hc := hp'.conj hq' ((isCodedSequent_singleton hn
    (negateFormula_mem membershipLanguageCode_valid hp.1)).insert hψχ) hp.2.1 hq.2.1
  exact ⟨hp.1, hψχ, hc.to_internal⟩

theorem HenkinAccepted.conj (hω : Schmerl.HasStandardOmega V) {T s n φ ψ : V}
    (hs : IsCoherentHenkinSequence T s) (hp : HenkinAccepted T s ⟨n, φ⟩ₖ)
    (hq : HenkinAccepted T s ⟨n, ψ⟩ₖ) : HenkinAccepted T s ⟨n, andCode φ ψ⟩ₖ := by
  have hφ := (mem_formulaSet_iff _ _ _ _).mpr hp.valid
  have hψ := (mem_formulaSet_iff _ _ _ _).mpr hq.valid
  have hn := formulaSet_context membershipLanguageCode_valid hφ
  obtain ⟨k, hk, hp, hq⟩ := hp.common_stage hω hs hq
  obtain ⟨a, ha, hea, hip⟩ := hp.2.2
  obtain ⟨b, hb, heb, hiq⟩ := hq.2.2
  rw [henkinLiftCode_context hn ha] at hea
  rw [henkinLiftCode_context hn hb] at heb
  have : IsOrdinal a := IsOrdinal.of_mem ha
  have : IsOrdinal b := IsOrdinal.of_mem hb
  have hab : a = b := ordinalAdd_right_injective (hea.symm.trans heb)
  subst b
  refine ⟨k, hk, (mem_formulaSet_iff _ _ _ _).mp (formulaSet_binary membershipLanguageCode_valid hn hφ hψ).1,
    hp.2.1, a, ha, ?_, ?_⟩
  · rwa [henkinLiftCode_context hn ha]
  · rw [henkinLiftCode_and hφ hψ ha, kpair.π₂_kpair]
    exact hip.conj hω hiq

theorem IsCoherentHenkinSequence.and_iff (hω : Schmerl.HasStandardOmega V) {T s n φ ψ : V}
    (hs : IsCoherentHenkinSequence T s)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n) :
    HenkinAccepted T s ⟨n, andCode φ ψ⟩ₖ ↔ HenkinAccepted T s ⟨n, φ⟩ₖ ∧ HenkinAccepted T s ⟨n, ψ⟩ₖ := by
  constructor
  · intro h
    exact ⟨h.consequence hω (CodedFormulaImplies.conj_left T hφ hψ),
      h.consequence hω (CodedFormulaImplies.conj_right T hφ hψ)⟩
  · exact fun h ↦ h.1.conj hω hs h.2

theorem IsCompleteHenkinSequence.or_iff (hω : Schmerl.HasStandardOmega V) {T s n φ ψ : V}
    (hs : IsCompleteHenkinSequence T s)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n) :
    HenkinAccepted T s ⟨n, orCode φ ψ⟩ₖ ↔ HenkinAccepted T s ⟨n, φ⟩ₖ ∨ HenkinAccepted T s ⟨n, ψ⟩ₖ := by
  have hn := formulaSet_context membershipLanguageCode_valid hφ
  have he := hs.negate_iff hω (formulaSet_binary membershipLanguageCode_valid hn hφ hψ).2
  rw [negateFormula_or membershipLanguageCode_valid hn hφ hψ,
    hs.1.and_iff hω (negateFormula_mem membershipLanguageCode_valid hφ)
      (negateFormula_mem membershipLanguageCode_valid hψ), hs.negate_iff hω hφ, hs.negate_iff hω hψ] at he
  tauto

theorem henkinLiftCode_falsity {n k : V} (hn : n ∈ (ω : V)) (hk : k ∈ (ω : V)) :
    kpair.π₂ (henkinLiftCode ⟨n, falsityCode⟩ₖ k) = falsityCode := by
  apply naturalNumber_induction (fun k ↦ kpair.π₂ (henkinLiftCode ⟨n, falsityCode⟩ₖ k) = falsityCode)
    (by definability) ?_ ?_ k hk
  · simp only [henkinLiftCode_zero, kpair.π₂_kpair]
  · intro k hk ih
    rw [henkinLiftCode_succ _ hk]
    simp only [henkinShiftCode, kpair.π₂_kpair, ih, henkinLiftCode_context hn hk, henkinShiftFormula,
      renameMembershipFormula_falsity (ordinalAdd_natural hn hk)]

theorem IsConsistentCodedFormula.not_falsity {T n : V}
    (h : IsConsistentCodedFormula T n falsityCode) : False := by
  apply h.2
  have ht : StandardCodedProvable (T ∪ canonicalEqualityOpenCodes) n
      {negateFormula membershipLanguageCode ∅ n falsityCode} := by
    rw [negateFormula_falsity membershipLanguageCode_valid h.context]
    exact StandardCodedProvable.verum _ h.context
  exact ht.to_internal

theorem IsCoherentHenkinSequence.not_falsity (hω : Schmerl.HasStandardOmega V) {T s n : V}
    (hs : IsCoherentHenkinSequence T s) : ¬HenkinAccepted T s ⟨n, falsityCode⟩ₖ := by
  rintro ⟨k, hk, hr⟩
  have hf := (mem_formulaSet_iff _ _ _ _).mpr hr.1
  have hn := formulaSet_context membershipLanguageCode_valid hf
  obtain ⟨a, ha, _, himp⟩ := hr.2.2
  rw [henkinLiftCode_falsity hn ha] at himp
  obtain ⟨m, ψ, he, _, hc⟩ := henkinConditions_cases (function_value_mem hs.1 hk)
  rw [he, kpair.π₁_kpair, kpair.π₂_kpair] at himp
  exact (himp.consistent hω hc).not_falsity

theorem IsCompleteHenkinSequence.truth (hω : Schmerl.HasStandardOmega V) {T s n : V}
    (hs : IsCompleteHenkinSequence T s) (hn : n ∈ (ω : V)) : HenkinAccepted T s ⟨n, truthCode⟩ₖ := by
  have he := hs.2 n truthCode (formulaSet_constants membershipLanguageCode_valid hn ∅).1
  rw [negateFormula_truth membershipLanguageCode_valid hn] at he
  exact he.resolve_right (hs.1.not_falsity hω)

end ZFVP
