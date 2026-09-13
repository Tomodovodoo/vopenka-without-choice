import ZFVP.ModelTheory.InternalHenkinNameRenaming

/-! Every axiom of the fixed open theory holds at every natural-name assignment. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem CodedFormulaImplies.of_provable {T n φ ψ : V}
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n)
    (hp : StandardCodedProvable (T ∪ canonicalEqualityOpenCodes) n {ψ}) : CodedFormulaImplies T n φ ψ := by
  have hn := formulaSet_context membershipLanguageCode_valid hφ
  have hv := (isCodedSequent_singleton hn (negateFormula_mem membershipLanguageCode_valid hφ)).insert hψ
  refine ⟨hφ, hψ, (hp.weaken hv ?_).to_internal⟩
  intro x hx
  exact mem_insert.mpr (Or.inl (mem_singleton_iff.mp hx))

theorem IsCompleteHenkinSequence.provable (hω : Schmerl.HasStandardOmega V) {T s n φ : V}
    (hs : IsCompleteHenkinSequence T s) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n)
    (hp : StandardCodedProvable (T ∪ canonicalEqualityOpenCodes) n {φ}) : HenkinAccepted T s ⟨n, φ⟩ₖ := by
  have hn := formulaSet_context membershipLanguageCode_valid hφ
  exact (hs.truth hω hn).consequence hω
    (CodedFormulaImplies.of_provable (formulaSet_constants membershipLanguageCode_valid hn ∅).1 hφ hp)

theorem IsCompleteHenkinSequence.name_provable (hω : Schmerl.HasStandardOmega V) {T s n φ b : V}
    (hs : IsCompleteHenkinSequence T s) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n)
    (hp : StandardCodedProvable (T ∪ canonicalEqualityOpenCodes) n {φ}) (hb : b ∈ (ω : V) ^ n) :
    HenkinNameHolds T s n φ b := by
  have hn := formulaSet_context membershipLanguageCode_valid hφ
  obtain ⟨m, hm, r, hr, he⟩ := exists_reverseNameAssignment hn hb
  rw [henkinNameHolds_iff_of_rep hω hs hφ hm hr he]
  have himp := (CodedFormulaImplies.of_provable
    (formulaSet_constants membershipLanguageCode_valid hn ∅).1 hφ hp).rename hω hm hr
  rw [renameMembershipFormula_truth hn] at himp
  exact (hs.truth hω hm).consequence hω himp

theorem IsCompleteHenkinSequence.name_axiom (hω : Schmerl.HasStandardOmega V) {T s n φ b : V}
    (hs : IsCompleteHenkinSequence T s) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n)
    (hmem : ⟨n, φ⟩ₖ ∈ T ∪ canonicalEqualityOpenCodes) (hb : b ∈ (ω : V) ^ n) :
    HenkinNameHolds T s n φ b :=
  hs.name_provable hω hφ (StandardCodedProvable.axiom (formulaSet_context membershipLanguageCode_valid hφ)
    ((mem_formulaSet_iff _ _ _ _).mp hφ) hmem) hb

end ZFVP
