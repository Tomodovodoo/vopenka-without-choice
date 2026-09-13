import ZFVP.ModelTheory.InternalHenkinNameTruth

/-! Boolean constructor equations for the Henkin truth table on natural names. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsCompleteHenkinSequence

theorem name_negate_iff (hω : Schmerl.HasStandardOmega V) {T s n φ b : V}
    (hs : IsCompleteHenkinSequence T s) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n)
    (hb : b ∈ (ω : V) ^ n) :
    HenkinNameHolds T s n (negateFormula membershipLanguageCode ∅ n φ) b ↔
      ¬HenkinNameHolds T s n φ b := by
  have hn := formulaSet_context membershipLanguageCode_valid hφ
  obtain ⟨m, hm, r, hr, he⟩ := exists_reverseNameAssignment hn hb
  rw [henkinNameHolds_iff_of_rep hω hs (negateFormula_mem membershipLanguageCode_valid hφ) hm hr he,
    henkinNameHolds_iff_of_rep hω hs hφ hm hr he, renameMembershipFormula_negate hn hm hr hφ,
    hs.negate_iff hω (renameMembershipFormula_mem hn hm hr hφ)]

theorem name_and_iff (hω : Schmerl.HasStandardOmega V) {T s n φ ψ b : V}
    (hs : IsCompleteHenkinSequence T s) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n)
    (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n) (hb : b ∈ (ω : V) ^ n) :
    HenkinNameHolds T s n (andCode φ ψ) b ↔ HenkinNameHolds T s n φ b ∧ HenkinNameHolds T s n ψ b := by
  have hn := formulaSet_context membershipLanguageCode_valid hφ
  obtain ⟨m, hm, r, hr, he⟩ := exists_reverseNameAssignment hn hb
  rw [henkinNameHolds_iff_of_rep hω hs (formulaSet_binary membershipLanguageCode_valid hn hφ hψ).1 hm hr he,
    henkinNameHolds_iff_of_rep hω hs hφ hm hr he, henkinNameHolds_iff_of_rep hω hs hψ hm hr he,
    renameMembershipFormula_and hφ hψ,
    hs.1.and_iff hω (renameMembershipFormula_mem hn hm hr hφ) (renameMembershipFormula_mem hn hm hr hψ)]

theorem name_or_iff (hω : Schmerl.HasStandardOmega V) {T s n φ ψ b : V}
    (hs : IsCompleteHenkinSequence T s) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n)
    (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n) (hb : b ∈ (ω : V) ^ n) :
    HenkinNameHolds T s n (orCode φ ψ) b ↔ HenkinNameHolds T s n φ b ∨ HenkinNameHolds T s n ψ b := by
  have hn := formulaSet_context membershipLanguageCode_valid hφ
  obtain ⟨m, hm, r, hr, he⟩ := exists_reverseNameAssignment hn hb
  rw [henkinNameHolds_iff_of_rep hω hs (formulaSet_binary membershipLanguageCode_valid hn hφ hψ).2 hm hr he,
    henkinNameHolds_iff_of_rep hω hs hφ hm hr he, henkinNameHolds_iff_of_rep hω hs hψ hm hr he,
    renameMembershipFormula_or hφ hψ,
    hs.or_iff hω (renameMembershipFormula_mem hn hm hr hφ) (renameMembershipFormula_mem hn hm hr hψ)]

theorem name_truth (hω : Schmerl.HasStandardOmega V) {T s n b : V}
    (hs : IsCompleteHenkinSequence T s) (hn : n ∈ (ω : V)) (hb : b ∈ (ω : V) ^ n) :
    HenkinNameHolds T s n truthCode b := by
  obtain ⟨m, hm, r, hr, he⟩ := exists_reverseNameAssignment hn hb
  rw [henkinNameHolds_iff_of_rep hω hs (formulaSet_constants membershipLanguageCode_valid hn ∅).1 hm hr he,
    renameMembershipFormula_truth hn]
  exact hs.truth hω hm

theorem name_not_falsity (hω : Schmerl.HasStandardOmega V) {T s n b : V}
    (hs : IsCompleteHenkinSequence T s) (hn : n ∈ (ω : V)) (hb : b ∈ (ω : V) ^ n) :
    ¬HenkinNameHolds T s n falsityCode b := by
  obtain ⟨m, hm, r, hr, he⟩ := exists_reverseNameAssignment hn hb
  rw [henkinNameHolds_iff_of_rep hω hs (formulaSet_constants membershipLanguageCode_valid hn ∅).2 hm hr he,
    renameMembershipFormula_falsity hn]
  exact hs.1.not_falsity hω

end IsCompleteHenkinSequence

end ZFVP
