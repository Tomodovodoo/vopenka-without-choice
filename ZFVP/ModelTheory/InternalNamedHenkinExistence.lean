import ZFVP.ModelTheory.InternalNamedWitnessSets
import ZFVP.ModelTheory.InternalNamedFilterUnion
import ZFVP.ModelTheory.InternalRasiowaSikorski

/-! Construct an actual complete named Henkin theory over a finitely realizable
background, while meeting any additional internally countable family of dense sets. -/

set_option autoImplicit false

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem namedDecisionDense_mem_henkinFamily {P L q : V}
    (hq : q ∈ namedFormulaSet L (ω : V)) :
    namedDecisionDense P L q ∈ namedHenkinDenseFamily P L :=
  mem_union_iff.mpr (Or.inl ((repl_spec _).mpr ⟨q, hq, rfl⟩))

theorem namedWitnessDense_mem_henkinFamily {P L q : V}
    (hq : q ∈ namedWitnessQueries L) :
    namedWitnessDense P L q ∈ namedHenkinDenseFamily P L :=
  mem_union_iff.mpr (Or.inr ((repl_spec _).mpr ⟨q, hq, rfl⟩))

theorem namedHenkinFilter_complete {L M j B G : V} (hL : IsLanguageCode L)
    (hG : IsForcingFilter (namedFiniteConditions L M j B)
      (reverseInclusionOrder (namedFiniteConditions L M j B)) G)
    (hmeet : ∀ D ∈ namedHenkinDenseFamily (namedFiniteConditions L M j B) L, ∃ A ∈ G, A ∈ D) :
    IsCompleteNamedTheory L M j B (⋃ˢ G) := by
  apply namedConditionFilter_sUnion_isCompleteNamedTheory hL hG
  · intro q hq
    exact hmeet _ (namedDecisionDense_mem_henkinFamily hq)
  · intro n hn φ hφ b hb
    obtain ⟨A, hA, hAW⟩ := hmeet _ (namedWitnessDense_mem_henkinFamily
      ((pair_mem_namedWitnessQueries L n φ b).mpr ⟨hn, hφ, hb⟩))
    exact ⟨A, hA, ((mem_namedWitnessDense_pair _ _ _ _ _ _).mp hAW).2⟩

theorem exists_completeNamedTheory_filter_with_extra_below (hAC : InternalChoice V)
    {L M j B E A₀ : V} (hL : IsLanguageCode L)
    (hF : IsInternallyCountable (functionSymbols L)) (hR : IsInternallyCountable (relationSymbols L))
    (hj : j ∈ (ω : V) ^ structureDomain M) (hfr : HasFreshBackgroundNames j B)
    (hE : IsInternallyCountable E)
    (hdE : ∀ D ∈ E, ForcingDense (namedFiniteConditions L M j B)
      (reverseInclusionOrder (namedFiniteConditions L M j B)) D)
    (hA₀ : A₀ ∈ namedFiniteConditions L M j B) :
    ∃ G : V, IsForcingFilter (namedFiniteConditions L M j B)
      (reverseInclusionOrder (namedFiniteConditions L M j B)) G ∧ A₀ ∈ G ∧
      IsCompleteNamedTheory L M j B (⋃ˢ G) ∧ ∀ D ∈ E, ∃ A ∈ G, A ∈ D := by
  have hcount : IsInternallyCountable (namedHenkinDenseFamily (namedFiniteConditions L M j B) L ∪ E) :=
    internallyCountable_union (namedHenkinDenseFamily_countable hAC hL hF hR) hE
  have hd : ∀ D ∈ namedHenkinDenseFamily (namedFiniteConditions L M j B) L ∪ E,
      ForcingDense (namedFiniteConditions L M j B)
        (reverseInclusionOrder (namedFiniteConditions L M j B)) D := by
    intro D hD
    rcases mem_union_iff.mp hD with hD | hD
    · exact namedHenkinDenseFamily_dense hL hj hfr D hD
    · exact hdE D hD
  obtain ⟨G, hG, hA₀G, hmeet⟩ := internal_rasiowaSikorski hAC
    (reverseInclusionOrder_poset (namedFiniteConditions L M j B)).1 hcount hd hA₀
  exact ⟨G, hG, hA₀G, namedHenkinFilter_complete hL hG
    (fun D hD ↦ hmeet D (mem_union_iff.mpr (Or.inl hD))),
    fun D hD ↦ hmeet D (mem_union_iff.mpr (Or.inr hD))⟩

theorem exists_completeNamedTheory_filter_with_extra (hAC : InternalChoice V)
    {L M j B E : V} (hL : IsLanguageCode L)
    (hF : IsInternallyCountable (functionSymbols L)) (hR : IsInternallyCountable (relationSymbols L))
    (hj : j ∈ (ω : V) ^ structureDomain M) (hB : FinitelySourceRealized L M j B)
    (hfr : HasFreshBackgroundNames j B) (hE : IsInternallyCountable E)
    (hdE : ∀ D ∈ E, ForcingDense (namedFiniteConditions L M j B)
      (reverseInclusionOrder (namedFiniteConditions L M j B)) D) :
    ∃ G : V, IsForcingFilter (namedFiniteConditions L M j B)
      (reverseInclusionOrder (namedFiniteConditions L M j B)) G ∧
      IsCompleteNamedTheory L M j B (⋃ˢ G) ∧ ∀ D ∈ E, ∃ A ∈ G, A ∈ D := by
  obtain ⟨G, hG, _, hT, hmeet⟩ := exists_completeNamedTheory_filter_with_extra_below
    hAC hL hF hR hj hfr hE hdE (empty_mem_namedFiniteConditions hB)
  exact ⟨G, hG, hT, hmeet⟩

theorem exists_completeNamedTheory (hAC : InternalChoice V)
    {L M j B : V} (hL : IsLanguageCode L)
    (hF : IsInternallyCountable (functionSymbols L)) (hR : IsInternallyCountable (relationSymbols L))
    (hj : j ∈ (ω : V) ^ structureDomain M) (hB : FinitelySourceRealized L M j B)
    (hfr : HasFreshBackgroundNames j B) : ∃ T : V, IsCompleteNamedTheory L M j B T := by
  obtain ⟨G, _, hT, _⟩ := exists_completeNamedTheory_filter_with_extra hAC hL hF hR hj hB hfr
    internallyCountable_empty (fun _ hD ↦ False.elim (not_mem_empty hD))
  exact ⟨⋃ˢ G, hT⟩

end ZFVP
