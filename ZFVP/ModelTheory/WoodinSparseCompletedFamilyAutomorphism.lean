import ZFVP.ModelTheory.WoodinSparseCompletedAutomorphism

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSparseCompletedFamilyAutomorphism (θ m : V) : V :=
  woodinSparseCompletedAutomorphism θ (woodinSparsePrefixCode θ)
    (woodinSparseInverseAutomorphism θ (woodinSparsePrefixCode θ) m)

instance woodinSparseCompletedFamilyAutomorphism_definable :
    ℒₛₑₜ-function₂[V] woodinSparseCompletedFamilyAutomorphism := by
  unfold woodinSparseCompletedFamilyAutomorphism
  apply Language.DefinableFunction₃.comp
  · definability
  · definability
  · apply Language.DefinableFunction₃.comp <;> definability

variable {Ω θ m : V} [IsOrdinal θ]
local notation "c" => woodinSparsePrefixCode θ
local notation "P" => woodinSparseInverseBase θ c
local notation "R" => woodinSparseInverseOrder θ c
local notation "f" => woodinSparseInverseAutomorphism θ c m
local notation "C" => woodinSparseCompletedInverseCarrier θ c
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
variable (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
variable (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
variable (hm : IsCoherentForcingAutomorphismFamily θ (woodinSparsePrefixCode θ) m)
variable (hmt : ∀ i ∈ θ, (m ‘ i) ‘ ∅ = ∅)

include hΩ hAC hθ h0 hlim hm hmt in
theorem woodinSparseInverseAutomorphism_fixes_empty : f ‘ ∅ = ∅ := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hp := ((woodinSparsePrefixCode_valid hΩ hAC hsub).system.tops.top ∅ hz).1
  rw [woodinSparsePrefixCode_top hΩ hAC hsub hz] at hp
  exact (woodinSparseActualInverseAutomorphism_section hΩ hAC hsub hm hz
    (ordinal_limit_of_not_successor hlim) hz hp).2.trans (hmt ∅ hz)

include hΩ hAC hθ h0 hlim hn hm hmt

theorem woodinSparseCompletedFamilyAutomorphism_automorphism :
    IsForcingAutomorphism ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
      ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ) (woodinSparseCompletedFamilyAutomorphism θ m) := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  exact woodinSparseCompletedAutomorphism_actual_stage hΩ hAC hθ h0 hlim hn
    (woodinSparseActualInverseAutomorphism hΩ hAC hsub hm hz (ordinal_limit_of_not_successor hlim))
    (woodinSparseInverseAutomorphism_fixes_empty hΩ hAC hθ h0 hlim hm hmt)

theorem woodinSparseCompletedFamilyAutomorphism_restrict {q : V}
    (hq : q ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ) :
    ((woodinSparseCompletedFamilyAutomorphism θ m) ‘ q) ↾ θ = f ‘ (q ↾ θ) := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  rw [(woodinSparseStageCode_inverse h0 hlim hn).1] at hq
  exact woodinSparseCompletedAutomorphism_restrict hΩ hAC hθ h0 hlim hn
    (woodinSparseActualInverseAutomorphism hΩ hAC hsub hm hz (ordinal_limit_of_not_successor hlim))
    (woodinSparseInverseAutomorphism_fixes_empty hΩ hAC hθ h0 hlim hm hmt) hq

theorem woodinSparseCompletedFamilyAutomorphism_base_section {p : V} (hp : p ∈ P) :
    p ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ ∧
      (woodinSparseCompletedFamilyAutomorphism θ m) ‘ p = f ‘ p := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  rw [(woodinSparseStageCode_inverse h0 hlim hn).1]
  exact woodinSparseCompletedAutomorphism_base_section hΩ hAC hθ h0 hlim hn
    (woodinSparseActualInverseAutomorphism hΩ hAC hsub hm hz (ordinal_limit_of_not_successor hlim))
    (woodinSparseInverseAutomorphism_fixes_empty hΩ hAC hθ h0 hlim hm hmt) hp

theorem woodinSparseCompletedFamilyAutomorphism_restrict_earlier {q i : V}
    (hq : q ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ) (hi : i ∈ θ) :
    ((woodinSparseCompletedFamilyAutomorphism θ m) ‘ q) ↾ (succ (woodinSourceIndex i)) =
      (m ‘ i) ‘ (q ↾ (succ (woodinSourceIndex i))) := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hl := ordinal_limit_of_not_successor hlim
  have hb : succ (woodinSourceIndex i) ⊆ θ := by
    simpa only [woodinSparseBounds_value hi] using woodinSparseBounds_limit_subset hz hl hi
  have hqc := hq
  rw [(woodinSparseStageCode_inverse h0 hlim hn).1] at hqc
  have hp := (mem_sparsePairCarrier_iff.mp hqc).2.1
  rw [← restrict_restrict_of_subset hb,
    woodinSparseCompletedFamilyAutomorphism_restrict hΩ hAC hθ h0 hlim hn hm hmt hq,
    woodinSparseActualInverseAutomorphism_restrict hΩ hAC hsub hm hz hl hp hi,
    restrict_restrict_of_subset hb]

theorem woodinSparseCompletedFamilyAutomorphism_section_earlier {p i : V}
    (hi : i ∈ θ) (hp : p ∈ (forcingCodeP c) ‘ i) :
    p ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ ∧
      (woodinSparseCompletedFamilyAutomorphism θ m) ‘ p = (m ‘ i) ‘ p := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hb := woodinSparseActualInverseAutomorphism_section hΩ hAC hsub hm hz
    (ordinal_limit_of_not_successor hlim) hi hp
  have hh := woodinSparseCompletedFamilyAutomorphism_base_section hΩ hAC hθ h0 hlim hn hm hmt hb.1
  exact ⟨hh.1, hh.2.trans hb.2⟩

theorem woodinSparseCompletedFamilyAutomorphism_top :
    (woodinSparseCompletedFamilyAutomorphism θ m) ‘ ∅ = ∅ := by
  have hp := (woodinSparseCompletedAutomorphism_inputs hΩ hAC hθ h0 hlim hn).2.1.1
  exact (woodinSparseCompletedFamilyAutomorphism_base_section hΩ hAC hθ h0 hlim hn hm hmt hp).2.trans
    (woodinSparseInverseAutomorphism_fixes_empty hΩ hAC hθ h0 hlim hm hmt)

end ZFVP
