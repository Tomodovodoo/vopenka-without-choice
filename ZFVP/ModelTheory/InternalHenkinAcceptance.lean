import ZFVP.ModelTheory.InternalHenkinRefinement

/-! The internally defined completed diagram determined by coherent Henkin
stages. It decides each formula and never accepts opposite literals. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsCoherentHenkinSequence (T s : V) : Prop :=
  s ∈ (henkinConditions T) ^ (ω : V) ∧ ∀ i ∈ (ω : V), ∀ j ∈ (ω : V), i ∈ succ j →
    HenkinRefines T (s ‘ i) (s ‘ j)

instance coherentHenkinSequence_definable : ℒₛₑₜ-relation[V] IsCoherentHenkinSequence := by
  unfold IsCoherentHenkinSequence
  definability

def HenkinAccepted (T s p : V) : Prop := ∃ k ∈ (ω : V), HenkinRefines T p (s ‘ k)

instance henkinAccepted_definable : ℒₛₑₜ-relation₃[V] HenkinAccepted := by
  unfold HenkinAccepted
  definability

noncomputable def henkinAcceptedCodes (T s : V) : V :=
  {p ∈ formulaFamily (membershipLanguageCode : V) ∅ ; HenkinAccepted T s p}

theorem henkinStages_coherent (hω : Schmerl.HasStandardOmega V) {T e : V}
    (hT : EqualityCodedSequentConsistent T)
    (he : e ∈ (formulaFamily (membershipLanguageCode : V) ∅) ^ (ω : V)) :
    IsCoherentHenkinSequence T (henkinStages T e) :=
  ⟨henkinStages_function hω hT he, fun _ _ _ hj hij ↦ henkinStages_refines hω hT he hj hij⟩

theorem HenkinAccepted.valid {T s p : V} (h : HenkinAccepted T s p) :
    p ∈ formulaFamily (membershipLanguageCode : V) ∅ := by
  obtain ⟨_, _, h⟩ := h
  exact h.1

theorem mem_henkinAcceptedCodes_iff (T s p : V) : p ∈ henkinAcceptedCodes T s ↔ HenkinAccepted T s p := by
  simp only [henkinAcceptedCodes, mem_sep_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.valid, h⟩⟩

instance henkinAcceptedCodes_definable : ℒₛₑₜ-function₂[V] henkinAcceptedCodes := by
  have he : ℒₛₑₜ-relation₃[V] (fun A T s ↦ ∀ p, p ∈ A ↔ HenkinAccepted T s p) := by definability
  apply Language.Definable.of_iff he
  intro v
  change v 0 = henkinAcceptedCodes (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_henkinAcceptedCodes_iff]

namespace HenkinAccepted

theorem stage {T s k : V} (hs : IsCoherentHenkinSequence T s) (hk : k ∈ (ω : V)) :
    HenkinAccepted T s (s ‘ k) :=
  ⟨k, hk, HenkinRefines.refl T (mem_sep_iff.mp (function_value_mem hs.1 hk)).1⟩

theorem of_refines (hω : Schmerl.HasStandardOmega V) {T s p q : V}
    (h : HenkinAccepted T s q) (hpq : HenkinRefines T p q) : HenkinAccepted T s p := by
  obtain ⟨k, hk, hq⟩ := h
  exact ⟨k, hk, hpq.trans hω hq⟩

theorem consequence (hω : Schmerl.HasStandardOmega V) {T s n φ ψ : V}
    (h : HenkinAccepted T s ⟨n, φ⟩ₖ) (himp : CodedFormulaImplies T n φ ψ) :
    HenkinAccepted T s ⟨n, ψ⟩ₖ := h.of_refines hω (HenkinRefines.of_implication himp)

theorem common_stage (hω : Schmerl.HasStandardOmega V) {T s p q : V}
    (hs : IsCoherentHenkinSequence T s) (hp : HenkinAccepted T s p) (hq : HenkinAccepted T s q) :
    ∃ k ∈ (ω : V), HenkinRefines T p (s ‘ k) ∧ HenkinRefines T q (s ‘ k) := by
  obtain ⟨i, hi, hp⟩ := hp
  obtain ⟨j, hj, hq⟩ := hq
  have : IsOrdinal i := IsOrdinal.of_mem hi
  have : IsOrdinal j := IsOrdinal.of_mem hj
  rcases IsOrdinal.mem_trichotomy i j with hij | rfl | hji
  · exact ⟨j, hj, hp.trans hω (hs.2 i hi j hj (mem_succ_iff.mpr (Or.inr hij))), hq⟩
  · exact ⟨i, hi, hp, hq⟩
  · exact ⟨i, hi, hp, hq.trans hω (hs.2 j hj i hi (mem_succ_iff.mpr (Or.inr hji)))⟩

end HenkinAccepted

theorem CodedFormulaImplies.not_both (hω : Schmerl.HasStandardOmega V) {T n φ ψ : V}
    (hc : IsConsistentCodedFormula T n φ) (hp : CodedFormulaImplies T n φ ψ)
    (hn : CodedFormulaImplies T n φ (negateFormula membershipLanguageCode ∅ n ψ)) : False := by
  have hpos := ((codedFormulaImplies_iff_standard hω _ _ _ _).mp hp).2.2
  have hneg := ((codedFormulaImplies_iff_standard hω _ _ _ _).mp hn).2.2
  have hr := hpos.cut hneg (by
    simpa using (isCodedSequent_singleton hc.context (negateFormula_mem membershipLanguageCode_valid hc.1))) hp.2.1
  have hr' : StandardCodedProvable (T ∪ canonicalEqualityOpenCodes) n
      {negateFormula membershipLanguageCode ∅ n φ} := by simpa using hr
  exact hc.2 hr'.to_internal

theorem HenkinAccepted.not_negate (hω : Schmerl.HasStandardOmega V) {T s n φ : V}
    (hs : IsCoherentHenkinSequence T s) (hp : HenkinAccepted T s ⟨n, φ⟩ₖ) :
    ¬HenkinAccepted T s ⟨n, negateFormula membershipLanguageCode ∅ n φ⟩ₖ := by
  intro hneg
  have hφ := (mem_formulaSet_iff _ _ _ _).mpr hp.valid
  have hn := formulaSet_context membershipLanguageCode_valid hφ
  obtain ⟨k, hk, hp, hneg⟩ := hp.common_stage hω hs hneg
  obtain ⟨m, ψ, hsk, _, hc⟩ := henkinConditions_cases (function_value_mem hs.1 hk)
  obtain ⟨a, ha, hea, hip⟩ := hp.2.2
  obtain ⟨b, hb, heb, hin⟩ := hneg.2.2
  rw [hsk, kpair.π₁_kpair] at hea heb
  rw [henkinLiftCode_context hn ha] at hea
  rw [henkinLiftCode_context hn hb] at heb
  have : IsOrdinal a := IsOrdinal.of_mem ha
  have : IsOrdinal b := IsOrdinal.of_mem hb
  have hab : a = b := ordinalAdd_right_injective (hea.symm.trans heb)
  subst b
  rw [hsk, kpair.π₁_kpair, kpair.π₂_kpair] at hip hin
  rw [henkinLiftCode_negate hφ ha, kpair.π₂_kpair, henkinLiftCode_context hn ha, ← hea] at hin
  exact hip.not_both hω hc hin

theorem henkinStages_decides (hω : Schmerl.HasStandardOmega V) {T e n φ : V}
    (hT : EqualityCodedSequentConsistent T)
    (he : e ∈ (formulaFamily (membershipLanguageCode : V) ∅) ^ (ω : V))
    (hrange : range e = formulaFamily (membershipLanguageCode : V) ∅)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) :
    HenkinAccepted T (henkinStages T e) ⟨n, φ⟩ₖ ∨
      HenkinAccepted T (henkinStages T e) ⟨n, negateFormula membershipLanguageCode ∅ n φ⟩ₖ := by
  have hq : ⟨n, φ⟩ₖ ∈ range e := hrange.symm ▸ (mem_formulaSet_iff _ _ _ _).mp hφ
  obtain ⟨k, hkq⟩ := mem_range_iff.mp hq
  have : IsFunction e := IsFunction.of_mem he
  have hk : k ∈ (ω : V) := (domain_eq_of_mem_function he) ▸ mem_domain_of_kpair_mem hkq
  have hv : e ‘ k = ⟨n, φ⟩ₖ := value_eq_of_kpair_mem hkq
  have hstep := henkinNextCode_decides hω (function_value_mem (henkinStages_function hω hT he) hk) hφ
  rw [← hv, ← henkinStages_succ T e hk] at hstep
  rcases hstep with hpos | hneg
  · exact Or.inl ⟨succ k, ω_succ_closed hk, by simpa only [hv] using hpos⟩
  · exact Or.inr ⟨succ k, ω_succ_closed hk, hneg⟩

theorem henkinStages_accepts_negate_iff (hω : Schmerl.HasStandardOmega V) {T e n φ : V}
    (hT : EqualityCodedSequentConsistent T)
    (he : e ∈ (formulaFamily (membershipLanguageCode : V) ∅) ^ (ω : V))
    (hrange : range e = formulaFamily (membershipLanguageCode : V) ∅)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) :
    HenkinAccepted T (henkinStages T e) ⟨n, negateFormula membershipLanguageCode ∅ n φ⟩ₖ ↔
      ¬HenkinAccepted T (henkinStages T e) ⟨n, φ⟩ₖ := by
  constructor
  · exact fun hneg hp ↦ hp.not_negate hω (henkinStages_coherent hω hT he) hneg
  · intro hp
    exact (henkinStages_decides hω hT he hrange hφ).resolve_left hp

end ZFVP
