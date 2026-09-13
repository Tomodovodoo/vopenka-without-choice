import ZFVP.ModelTheory.InternalHenkinLiftAlgebra
import ZFVP.SetTheory.NaturalArithmeticLaws

/-! Later Henkin stages imply every earlier stage after extending its context. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def HenkinRefines (T p q : V) : Prop :=
  p ∈ formulaFamily (membershipLanguageCode : V) ∅ ∧
  q ∈ formulaFamily (membershipLanguageCode : V) ∅ ∧
    ∃ k ∈ (ω : V), kpair.π₁ q = kpair.π₁ (henkinLiftCode p k) ∧
      CodedFormulaImplies T (kpair.π₁ q) (kpair.π₂ q) (kpair.π₂ (henkinLiftCode p k))

instance henkinRefines_definable : ℒₛₑₜ-relation₃[V] HenkinRefines := by
  unfold HenkinRefines
  definability

namespace HenkinRefines

theorem refl (T : V) {p : V} (hp : p ∈ formulaFamily (membershipLanguageCode : V) ∅) :
    HenkinRefines T p p := by
  obtain ⟨n, _, φ, rfl⟩ := formulaFamily_context membershipLanguageCode_valid ∅ hp
  refine ⟨hp, hp, 0, by simp, ?_, ?_⟩
  · rw [henkinLiftCode_zero]
  · simp only [henkinLiftCode_zero, kpair.π₁_kpair, kpair.π₂_kpair]
    exact CodedFormulaImplies.refl T ((mem_formulaSet_iff _ _ _ _).mpr hp)

theorem of_implication {T n φ ψ : V} (h : CodedFormulaImplies T n φ ψ) :
    HenkinRefines T ⟨n, ψ⟩ₖ ⟨n, φ⟩ₖ := by
  refine ⟨(mem_formulaSet_iff _ _ _ _).mp h.2.1, (mem_formulaSet_iff _ _ _ _).mp h.1, 0, by simp, ?_, ?_⟩
  · simp only [henkinLiftCode_zero, kpair.π₁_kpair]
  · simpa only [henkinLiftCode_zero, kpair.π₁_kpair, kpair.π₂_kpair] using h

theorem lift (T : V) {p k : V} (hp : p ∈ formulaFamily (membershipLanguageCode : V) ∅)
    (hk : k ∈ (ω : V)) : HenkinRefines T p (henkinLiftCode p k) := by
  obtain ⟨n, _, φ, rfl⟩ := formulaFamily_context membershipLanguageCode_valid ∅ hp
  have hv := henkinLiftCode_valid ((mem_formulaSet_iff _ _ _ _).mpr hp) hk
  have hpair := henkinLiftCode_pair n φ hk
  have hmem : henkinLiftCode ⟨n, φ⟩ₖ k ∈ formulaFamily (membershipLanguageCode : V) (∅ : V) := by
    rw [hpair]
    exact (mem_formulaSet_iff _ _ _ _).mp hv
  exact ⟨hp, hmem, k, hk, rfl, CodedFormulaImplies.refl T hv⟩

theorem trans (hω : Schmerl.HasStandardOmega V) {T p q r : V}
    (h : HenkinRefines T p q) (g : HenkinRefines T q r) : HenkinRefines T p r := by
  obtain ⟨n, hn, φ, rfl⟩ := formulaFamily_context membershipLanguageCode_valid ∅ h.1
  obtain ⟨m, hm, ψ, rfl⟩ := formulaFamily_context membershipLanguageCode_valid ∅ h.2.1
  obtain ⟨l, _, χ, rfl⟩ := formulaFamily_context membershipLanguageCode_valid ∅ g.2.1
  obtain ⟨a, ha, hea, hpa⟩ := h.2.2
  obtain ⟨b, hb, heb, hqb⟩ := g.2.2
  simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hea hpa heb hqb
  have hm' : m = ordinalAdd n a := by simpa only [henkinLiftCode_context hn ha] using hea
  have hl' : l = ordinalAdd m b := by simpa only [henkinLiftCode_context hm hb] using heb
  have hpbase : ⟨m, kpair.π₂ (henkinLiftCode ⟨n, φ⟩ₖ a)⟩ₖ = henkinLiftCode ⟨n, φ⟩ₖ a := by
    rw [hea]
    exact (henkinLiftCode_pair n φ ha).symm
  have hpl := hpa.lift hω hb
  rw [hpbase, henkinLiftCode_add _ ha hb, ← hl'] at hpl
  refine ⟨h.1, g.2.1, ordinalAdd a b, ordinalAdd_natural ha hb, ?_, ?_⟩
  · simp only [kpair.π₁_kpair, henkinLiftCode_context hn (ordinalAdd_natural ha hb)]
    rw [hl', hm', ordinalAdd_assoc_natural hn ha hb]
  · simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    exact hqb.trans hω hpl

end HenkinRefines

theorem henkinWitnessCode_refines_literal (hω : Schmerl.HasStandardOmega V) {T n φ χ : V}
    (hzero : (0 : V) ∈ n) (hc : IsConsistentCodedFormula T n (andCode χ φ)) :
    HenkinRefines T ⟨n, χ⟩ₖ (henkinWitnessCode n φ χ) := by
  classical
  have hv := (andCode_mem_iff membershipLanguageCode_valid).mp hc.1
  have hnext := henkinWitnessCode_consistent hω hzero hc
  refine ⟨(mem_formulaSet_iff _ _ _ _).mp hv.2.1, (mem_sep_iff.mp hnext).1, ?_⟩
  by_cases he : χ = existsCode (kpair.π₂ χ)
  · have hbody := (existsCode_mem_iff membershipLanguageCode_valid).mp (he ▸ hv.2.1)
    have himp := (CodedFormulaImplies.conj_left T hbody.2 (henkinShiftFormula_valid hv.1 hv.2.2)).trans hω
      (CodedFormulaImplies.witness_exists T hv.1 hbody.2)
    rw [← he] at himp
    refine ⟨succ 0, by simp, ?_, ?_⟩
    · simp only [henkinWitnessCode, ite_eq_left he, henkinLiftCode_succ _ (show (0 : V) ∈ (ω : V) by simp),
        henkinLiftCode_zero, henkinShiftCode, kpair.π₁_kpair]
    · simpa only [henkinWitnessCode, ite_eq_left he,
        henkinLiftCode_succ _ (show (0 : V) ∈ (ω : V) by simp), henkinLiftCode_zero,
        henkinShiftCode, kpair.π₁_kpair, kpair.π₂_kpair] using himp
  · refine ⟨0, by simp, ?_, ?_⟩
    · simp only [henkinWitnessCode, ite_eq_right he, henkinLiftCode_zero, kpair.π₁_kpair]
    · simpa only [henkinWitnessCode, ite_eq_right he, henkinLiftCode_zero, kpair.π₁_kpair, kpair.π₂_kpair] using
        CodedFormulaImplies.conj_left T hv.2.1 hv.2.2

theorem henkinNextCode_decides (hω : Schmerl.HasStandardOmega V) {T p n ψ : V}
    (hp : p ∈ henkinConditions T) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n) :
    HenkinRefines T ⟨n, ψ⟩ₖ (henkinNextCode T p ⟨n, ψ⟩ₖ) ∨
    HenkinRefines T ⟨n, negateFormula membershipLanguageCode ∅ n ψ⟩ₖ (henkinNextCode T p ⟨n, ψ⟩ₖ) := by
  classical
  obtain ⟨m, φ, rfl, hzero, hφ⟩ := henkinConditions_cases hp
  have hm := hφ.context
  have hn := formulaSet_context membershipLanguageCode_valid hψ
  let a := henkinLiftCode ⟨m, φ⟩ₖ (succ n)
  let b := henkinLiftCode ⟨n, ψ⟩ₖ (succ m)
  let χ := henkinDecisionLiteral T (kpair.π₁ a) (kpair.π₂ a) (kpair.π₂ b)
  have ha := henkinLiftCode_consistent hω hφ hzero (ω_succ_closed hn)
  have hb := henkinLiftCode_valid hψ (ω_succ_closed hm)
  have he : kpair.π₁ b = kpair.π₁ a := by
    dsimp only [a, b]
    rw [henkinLiftCode_context hn (ω_succ_closed hm), henkinLiftCode_context hm (ω_succ_closed hn)]
    have : IsOrdinal n := IsOrdinal.of_mem hn
    have : IsOrdinal m := IsOrdinal.of_mem hm
    rw [ordinalAdd_succ, ordinalAdd_succ, ordinalAdd_comm_natural hn hm]
  have hb' : kpair.π₂ b ∈ formulaSet membershipLanguageCode ∅ (kpair.π₁ a) := he ▸ hb
  have hw := henkinWitnessCode_refines_literal hω ha.1 (henkinDecisionLiteral_consistent hω ha.2 hb')
  change HenkinRefines T ⟨kpair.π₁ a, χ⟩ₖ (henkinWitnessCode (kpair.π₁ a) (kpair.π₂ a) χ) at hw
  simp only [henkinNextCode, kpair.π₁_kpair]
  change HenkinRefines T ⟨n, ψ⟩ₖ (henkinWitnessCode (kpair.π₁ a) (kpair.π₂ a) χ) ∨
    HenkinRefines T ⟨n, negateFormula membershipLanguageCode ∅ n ψ⟩ₖ
      (henkinWitnessCode (kpair.π₁ a) (kpair.π₂ a) χ)
  by_cases hchoice : IsConsistentCodedFormula T (kpair.π₁ a) (andCode (kpair.π₂ a) (kpair.π₂ b))
  · have hχ : χ = kpair.π₂ b := by simp only [χ, henkinDecisionLiteral, ite_eq_left hchoice]
    have hcode : ⟨kpair.π₁ a, χ⟩ₖ = b := by
      rw [hχ, ← he]
      exact (henkinLiftCode_pair n ψ (ω_succ_closed hm)).symm
    rw [hcode] at hw
    exact Or.inl ((HenkinRefines.lift T ((mem_formulaSet_iff _ _ _ _).mp hψ) (ω_succ_closed hm)).trans hω hw)
  · have hχ : χ = negateFormula membershipLanguageCode ∅ (kpair.π₁ a) (kpair.π₂ b) := by
      simp only [χ, henkinDecisionLiteral, ite_eq_right hchoice]
    have hcode : ⟨kpair.π₁ a, χ⟩ₖ = henkinLiftCode ⟨n, negateFormula membershipLanguageCode ∅ n ψ⟩ₖ (succ m) := by
      rw [henkinLiftCode_negate hψ (ω_succ_closed hm), hχ, ← he]
    rw [hcode] at hw
    exact Or.inr ((HenkinRefines.lift T ((mem_formulaSet_iff _ _ _ _).mp
      (negateFormula_mem membershipLanguageCode_valid hψ)) (ω_succ_closed hm)).trans hω hw)

theorem henkinNextCode_refines (hω : Schmerl.HasStandardOmega V) {T p q : V}
    (hp : p ∈ henkinConditions T) (hq : q ∈ formulaFamily (membershipLanguageCode : V) ∅) :
    HenkinRefines T p (henkinNextCode T p q) := by
  classical
  have hnext := henkinNextCode_consistent hω hp hq
  refine ⟨(mem_sep_iff.mp hp).1, (mem_sep_iff.mp hnext).1, ?_⟩
  obtain ⟨n, φ, rfl, hzero, hφ⟩ := henkinConditions_cases hp
  obtain ⟨m, hm, ψ, rfl⟩ := formulaFamily_context membershipLanguageCode_valid ∅ hq
  have hn := hφ.context
  let a := henkinLiftCode ⟨n, φ⟩ₖ (succ m)
  let b := henkinLiftCode ⟨m, ψ⟩ₖ (succ n)
  let χ := henkinDecisionLiteral T (kpair.π₁ a) (kpair.π₂ a) (kpair.π₂ b)
  have ha := henkinLiftCode_valid hφ.1 (ω_succ_closed hm)
  have hc : IsConsistentCodedFormula T (kpair.π₁ a) (andCode χ (kpair.π₂ a)) := by
    have hb := henkinLiftCode_valid ((mem_formulaSet_iff _ _ _ _).mpr hq) (ω_succ_closed hn)
    have he : kpair.π₁ b = kpair.π₁ a := by
      dsimp only [a, b]
      rw [henkinLiftCode_context hm (ω_succ_closed hn), henkinLiftCode_context hn (ω_succ_closed hm)]
      have : IsOrdinal n := IsOrdinal.of_mem hn
      have : IsOrdinal m := IsOrdinal.of_mem hm
      rw [ordinalAdd_succ, ordinalAdd_succ, ordinalAdd_comm_natural hm hn]
    rw [he] at hb
    exact henkinDecisionLiteral_consistent hω
      (henkinLiftCode_consistent hω hφ hzero (ω_succ_closed hm)).2 hb
  have hχ := ((andCode_mem_iff membershipLanguageCode_valid).mp hc.1).2.1
  simp only [henkinNextCode, kpair.π₁_kpair]
  change ∃ k ∈ (ω : V),
    kpair.π₁ (henkinWitnessCode (kpair.π₁ a) (kpair.π₂ a) χ) = kpair.π₁ (henkinLiftCode ⟨n, φ⟩ₖ k) ∧
    CodedFormulaImplies T (kpair.π₁ (henkinWitnessCode (kpair.π₁ a) (kpair.π₂ a) χ))
      (kpair.π₂ (henkinWitnessCode (kpair.π₁ a) (kpair.π₂ a) χ)) (kpair.π₂ (henkinLiftCode ⟨n, φ⟩ₖ k))
  by_cases he : χ = existsCode (kpair.π₂ χ)
  · refine ⟨succ (succ m), ω_succ_closed (ω_succ_closed hm), ?_, ?_⟩
    · simp only [henkinWitnessCode, ite_eq_left he, henkinLiftCode_succ _ (ω_succ_closed hm),
        henkinShiftCode, kpair.π₁_kpair, a]
    · have hbdy := (existsCode_mem_iff membershipLanguageCode_valid).mp (he ▸ hχ)
      simpa only [henkinWitnessCode, ite_eq_left he, henkinLiftCode_succ _ (ω_succ_closed hm),
        henkinShiftCode, kpair.π₁_kpair, kpair.π₂_kpair, a] using
        CodedFormulaImplies.conj_right T hbdy.2 (henkinShiftFormula_valid hc.context ha)
  · refine ⟨succ m, ω_succ_closed hm, ?_, ?_⟩
    · simp only [henkinWitnessCode, ite_eq_right he, kpair.π₁_kpair, a]
    · simpa only [henkinWitnessCode, ite_eq_right he, kpair.π₁_kpair, kpair.π₂_kpair, a] using
        CodedFormulaImplies.conj_right T hχ ha

theorem henkinStages_refines (hω : Schmerl.HasStandardOmega V) {T e : V}
    (hT : EqualityCodedSequentConsistent T)
    (he : e ∈ (formulaFamily (membershipLanguageCode : V) ∅) ^ (ω : V))
    {i j : V} (hj : j ∈ (ω : V)) (hi : i ∈ succ j) :
    HenkinRefines T ((henkinStages T e) ‘ i) ((henkinStages T e) ‘ j) := by
  have hcon := henkinStages_function hω hT he
  have hvalid (k : V) (hk : k ∈ (ω : V)) :
      (henkinStages T e) ‘ k ∈ formulaFamily (membershipLanguageCode : V) ∅ :=
    (mem_sep_iff.mp (function_value_mem hcon hk)).1
  apply naturalNumber_induction (fun j ↦ ∀ i ∈ succ j,
    HenkinRefines T ((henkinStages T e) ‘ i) ((henkinStages T e) ‘ j)) (by definability) ?_ ?_ j hj i hi
  · intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact HenkinRefines.refl T (hvalid 0 (by simp))
    · exact (not_mem_empty hi).elim
  · intro j hj ih i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact HenkinRefines.refl T (hvalid (succ j) (ω_succ_closed hj))
    · have hstep := henkinNextCode_refines hω (function_value_mem hcon hj) (function_value_mem he hj)
      rw [← henkinStages_succ T e hj] at hstep
      exact (ih i hi).trans hω hstep

end ZFVP
