import ZFVP.ModelTheory.InternalHenkinStep
import ZFVP.ModelTheory.SchmerlInternalCodedSyntaxCountable
import ZFVP.SetTheory.SequenceCollapseAbsorption

/-! The Henkin construction is an actual internal function on omega. Its
recursion uses the definable decision and witness operation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def henkinStateStep (T e x : V) : V :=
  ⟨succ (kpair.π₁ x), henkinNextCode T (kpair.π₂ x) (e ‘ (kpair.π₁ x))⟩ₖ

instance henkinStateStep_definable : ℒₛₑₜ-function₃[V] henkinStateStep := by
  unfold henkinStateStep
  definability

noncomputable def henkinStateCode (T e k : V) : V :=
  naturalIteration (henkinStateStep T e) (by definability) ⟨0, ⟨1, truthCode⟩ₖ⟩ₖ k

instance henkinStateCode_definable (T e : V) : ℒₛₑₜ-function₁[V] (henkinStateCode T e) := by
  unfold henkinStateCode
  definability

theorem henkinStateCode_zero (T e : V) : henkinStateCode T e 0 = ⟨0, ⟨1, truthCode⟩ₖ⟩ₖ :=
  naturalIteration_zero _ _ _

theorem henkinStateCode_succ (T e : V) {k : V} (hk : k ∈ (ω : V)) :
    henkinStateCode T e (succ k) = henkinStateStep T e (henkinStateCode T e k) :=
  naturalIteration_succ _ _ _ hk

theorem henkinStateCode_index (T e : V) {k : V} (hk : k ∈ (ω : V)) :
    kpair.π₁ (henkinStateCode T e k) = k := by
  apply naturalNumber_induction (fun k ↦ kpair.π₁ (henkinStateCode T e k) = k)
    (by definability) ?_ ?_ k hk
  · simp only [henkinStateCode_zero, kpair.π₁_kpair]
  · intro k hk ih
    simp only [henkinStateCode_succ _ _ hk, henkinStateStep, kpair.π₁_kpair, ih]

noncomputable def henkinStageCode (T e k : V) : V := kpair.π₂ (henkinStateCode T e k)

instance henkinStageCode_definable (T e : V) : ℒₛₑₜ-function₁[V] (henkinStageCode T e) := by
  unfold henkinStageCode
  definability

theorem henkinStageCode_zero (T e : V) : henkinStageCode T e 0 = ⟨1, truthCode⟩ₖ := by
  simp only [henkinStageCode, henkinStateCode_zero, kpair.π₂_kpair]

theorem henkinStageCode_succ (T e : V) {k : V} (hk : k ∈ (ω : V)) :
    henkinStageCode T e (succ k) = henkinNextCode T (henkinStageCode T e k) (e ‘ k) := by
  simp only [henkinStageCode, henkinStateCode_succ _ _ hk, henkinStateStep,
    kpair.π₂_kpair, henkinStateCode_index _ _ hk]

theorem henkinStageCode_consistent (hω : Schmerl.HasStandardOmega V) {T e : V}
    (hT : EqualityCodedSequentConsistent T)
    (he : e ∈ (formulaFamily (membershipLanguageCode : V) ∅) ^ (ω : V))
    {k : V} (hk : k ∈ (ω : V)) : henkinStageCode T e k ∈ henkinConditions T := by
  apply naturalNumber_induction (fun k ↦ henkinStageCode T e k ∈ henkinConditions T)
    (by definability) ?_ ?_ k hk
  · rw [henkinStageCode_zero, pair_mem_henkinConditions_iff]
    exact ⟨by simp, hT.initialCondition hω⟩
  · intro k hk ih
    rw [henkinStageCode_succ _ _ hk]
    exact henkinNextCode_consistent hω ih (function_value_mem he hk)

noncomputable def henkinStages (T e : V) : V :=
  definableGraph (ω : V) (henkinStageCode T e) (by definability)

instance henkinStages_isFunction (T e : V) : IsFunction (henkinStages T e) :=
  definableGraph_isFunction _ _ _

@[simp] theorem henkinStages_domain (T e : V) : domain (henkinStages T e) = ω :=
  domain_definableGraph _ _ _

theorem henkinStages_value (T e : V) {k : V} (hk : k ∈ (ω : V)) :
    (henkinStages T e) ‘ k = henkinStageCode T e k := value_definableGraph _ _ _ hk

theorem henkinStages_function (hω : Schmerl.HasStandardOmega V) {T e : V}
    (hT : EqualityCodedSequentConsistent T)
    (he : e ∈ (formulaFamily (membershipLanguageCode : V) ∅) ^ (ω : V)) :
    henkinStages T e ∈ (henkinConditions T) ^ (ω : V) :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ hk ↦ henkinStageCode_consistent hω hT he hk)

theorem henkinStages_zero (T e : V) : (henkinStages T e) ‘ 0 = ⟨1, truthCode⟩ₖ := by
  rw [henkinStages_value _ _ (by simp), henkinStageCode_zero]

theorem henkinStages_succ (T e : V) {k : V} (hk : k ∈ (ω : V)) :
    (henkinStages T e) ‘ (succ k) = henkinNextCode T ((henkinStages T e) ‘ k) (e ‘ k) := by
  rw [henkinStages_value _ _ (ω_succ_closed hk), henkinStageCode_succ _ _ hk, henkinStages_value _ _ hk]

theorem henkinStages_context_grows (hω : Schmerl.HasStandardOmega V) {T e : V}
    (hT : EqualityCodedSequentConsistent T)
    (he : e ∈ (formulaFamily (membershipLanguageCode : V) ∅) ^ (ω : V))
    {k : V} (hk : k ∈ (ω : V)) :
    kpair.π₁ ((henkinStages T e) ‘ k) ∈ kpair.π₁ ((henkinStages T e) ‘ (succ k)) := by
  rw [henkinStages_succ _ _ hk]
  exact henkinNextCode_context_grows (function_value_mem (henkinStages_function hω hT he) hk)
    (function_value_mem he hk)

theorem henkinStages_context_covers (hω : Schmerl.HasStandardOmega V) {T e : V}
    (hT : EqualityCodedSequentConsistent T)
    (he : e ∈ (formulaFamily (membershipLanguageCode : V) ∅) ^ (ω : V))
    {k : V} (hk : k ∈ (ω : V)) : k ∈ kpair.π₁ ((henkinStages T e) ‘ k) := by
  apply naturalNumber_induction (fun k ↦ k ∈ kpair.π₁ ((henkinStages T e) ‘ k))
    (by definability) ?_ ?_ k hk
  · simp only [henkinStages_zero, kpair.π₁_kpair]
    simp
  · intro k hk ih
    have hc := function_value_mem (henkinStages_function hω hT he) hk
    obtain ⟨n, φ, hn, _, hφ⟩ := henkinConditions_cases hc
    have : IsOrdinal n := IsOrdinal.of_mem hφ.context
    have : IsOrdinal k := IsOrdinal.of_mem hk
    have hlt := henkinStages_context_grows hω hT he hk
    rw [hn, kpair.π₁_kpair] at ih hlt
    have hs : succ k ⊆ n := by
      intro x hx
      rcases mem_succ_iff.mp hx with rfl | hx
      · exact ih
      · exact IsOrdinal.toIsTransitive.mem_trans hx ih
    rcases IsOrdinal.subset_iff.mp hs with hEq | hMem
    · exact hEq ▸ hlt
    · have hc' := function_value_mem (henkinStages_function hω hT he) (ω_succ_closed hk)
      obtain ⟨m, ψ, hm, _, hψ⟩ := henkinConditions_cases hc'
      have : IsOrdinal m := IsOrdinal.of_mem hψ.context
      rw [hm, kpair.π₁_kpair] at hlt ⊢
      exact IsOrdinal.toIsTransitive.mem_trans hMem hlt

theorem membershipFormulaFamily_countable (hAC : InternalChoice V) :
    IsInternallyCountable (formulaFamily (membershipLanguageCode : V) (∅ : V)) := by
  apply Schmerl.formulaFamily_countable hAC membershipLanguageCode_valid
  · simpa [membershipLanguageCode] using (internallyCountable_empty (V := V))
  · have hc : IsInternallyCountable (2 : V) := internallyCountable_subset internallyCountable_omega
      (IsOrdinal.toIsTransitive.transitive (2 : V) (by simp))
    simpa [membershipLanguageCode] using hc
  · exact internallyCountable_empty

theorem exists_internal_henkinStages (hω : Schmerl.HasStandardOmega V) (hAC : InternalChoice V)
    {T : V} (hT : EqualityCodedSequentConsistent T) :
    ∃ e ∈ (formulaFamily (membershipLanguageCode : V) ∅) ^ (ω : V),
      range e = formulaFamily membershipLanguageCode ∅ ∧
      ∃ s ∈ (henkinConditions T) ^ (ω : V), s ‘ 0 = ⟨1, truthCode⟩ₖ ∧
        (∀ k ∈ (ω : V), s ‘ (succ k) = henkinNextCode T (s ‘ k) (e ‘ k)) ∧
        ∀ k ∈ (ω : V), k ∈ kpair.π₁ (s ‘ k) := by
  have hi : (⟨(1 : V), truthCode⟩ₖ : V) ∈ formulaFamily membershipLanguageCode ∅ :=
    (mem_formulaSet_iff _ _ _ _).mp (hT.initialCondition hω).1
  obtain ⟨e, he, hr⟩ := exists_surjection_of_cardLE (membershipFormulaFamily_countable hAC) hi
  exact ⟨e, he, hr, henkinStages T e, henkinStages_function hω hT he,
    henkinStages_zero T e, fun _ hk ↦ henkinStages_succ T e hk,
    fun _ hk ↦ henkinStages_context_covers hω hT he hk⟩

end ZFVP
