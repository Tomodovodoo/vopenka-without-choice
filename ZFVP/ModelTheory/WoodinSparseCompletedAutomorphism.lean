import ZFVP.ModelTheory.WoodinSparseAutomorphismHartogs
import ZFVP.ModelTheory.WoodinSparseActualLimitAutomorphisms
import ZFVP.ModelTheory.WoodinSparseOwnCutoffs

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSparseCompletedAutomorphism (θ c f : V) : V :=
  sparseHartogsAutomorphism θ (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c) ∅
    (woodinLimitCardinal (woodinIterationCardinalPrefix θ)) (woodinSparseInverseCutoff θ c) f

instance woodinSparseCompletedAutomorphism_definable : ℒₛₑₜ-function₃[V] woodinSparseCompletedAutomorphism := by
  unfold woodinSparseCompletedAutomorphism
  apply sparseHartogsAutomorphism_comp_definable <;> definability

variable {Ω θ f : V} [IsOrdinal θ]
local notation "c" => woodinSparsePrefixCode θ
local notation "P" => woodinSparseInverseBase θ c
local notation "R" => woodinSparseInverseOrder θ c
local notation "δ" => woodinSparseInverseCutoff θ c
local notation "C" => woodinSparseCompletedInverseCarrier θ c
local notation "T" => woodinSparseCompletedInverseOrder θ c
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
variable (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
variable (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))

include hΩ hAC hθ h0 hlim hn in
theorem woodinSparseCompletedAutomorphism_inputs :
    IsForcingPreorder P R ∧ IsForcingTop P R ∅ ∧ IsChoicelessInaccessible δ ∧
      P ∈ hierarchy δ ∧ ∀ p ∈ P, IsSparseFunctionOn θ p := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hl := ordinal_limit_of_not_successor hlim
  have hb := woodinSparsePrefix_inverse_base_laws hΩ hAC hsub hz hl
  have he := woodinSparsePrefix_inverse_cutoff hΩ hAC hsub h0 hlim hn
  refine ⟨hb.1, hb.2, ?_, ?_, ?_⟩
  · rw [he]
    exact ((woodinIterationExit hΩ hAC).2.1 θ hθ).1.inaccessible θ (mem_succ_self θ)
  · rw [he]
    exact woodinSparsePrefix_inverse_base_small hΩ hAC hθ h0 hlim hn
  · intro p hp
    exact ((mem_woodinSparseInverseBase_iff (woodinSparsePrefixCode_valid hΩ hAC hsub)).mp hp).1

variable (hf : IsForcingAutomorphism (woodinSparseInverseBase θ (woodinSparsePrefixCode θ))
  (woodinSparseInverseOrder θ (woodinSparsePrefixCode θ)) f) (hft : f ‘ ∅ = ∅)

include hΩ hAC hθ h0 hlim hn hf hft

theorem woodinSparseCompletedAutomorphism_automorphism :
    IsForcingAutomorphism C T (woodinSparseCompletedAutomorphism θ c f) := by
  obtain ⟨hR, ht, hδ, hP, hsp⟩ := woodinSparseCompletedAutomorphism_inputs hΩ hAC hθ h0 hlim hn
  exact sparseHartogsAutomorphism_automorphism hf hR ht hft hδ hP hsp

theorem woodinSparseCompletedAutomorphism_value {q : V} (hq : q ∈ C) :
    (woodinSparseCompletedAutomorphism θ c f) ‘ q =
      sparseAppend θ (f ‘ (q ↾ θ)) (normalizedIsomorphismName P R ∅ f (q ‘ θ)) := by
  obtain ⟨hR, ht, hδ, hP, hsp⟩ := woodinSparseCompletedAutomorphism_inputs hΩ hAC hθ h0 hlim hn
  exact sparseHartogsAutomorphism_value hf hR ht hft hδ hP hsp hq

theorem woodinSparseCompletedAutomorphism_restrict {q : V} (hq : q ∈ C) :
    ((woodinSparseCompletedAutomorphism θ c f) ‘ q) ↾ θ = f ‘ (q ↾ θ) := by
  obtain ⟨hR, ht, hδ, hP, hsp⟩ := woodinSparseCompletedAutomorphism_inputs hΩ hAC hθ h0 hlim hn
  exact sparseHartogsAutomorphism_restrict hf hR ht hft hδ hP hsp hq

theorem woodinSparseCompletedAutomorphism_empty_tail {q : V} (hq : q ∈ C) (hqa : q ‘ θ = ∅) :
    (woodinSparseCompletedAutomorphism θ c f) ‘ q = f ‘ (q ↾ θ) := by
  obtain ⟨hR, ht, hδ, hP, hsp⟩ := woodinSparseCompletedAutomorphism_inputs hΩ hAC hθ h0 hlim hn
  exact sparseHartogsAutomorphism_empty_tail hf hR ht hft hδ hP hsp hq hqa

theorem woodinSparseCompletedAutomorphism_inverse_value {q : V} (hq : q ∈ C) :
    (woodinSparseCompletedAutomorphism θ c (converseGraph f)) ‘
      ((woodinSparseCompletedAutomorphism θ c f) ‘ q) = q := by
  obtain ⟨hR, ht, hδ, hP, hsp⟩ := woodinSparseCompletedAutomorphism_inputs hΩ hAC hθ h0 hlim hn
  exact sparseHartogsAutomorphism_inverse_value hf hR ht hft hδ hP hsp hq

theorem woodinSparseCompletedAutomorphism_actual_stage :
    IsForcingAutomorphism ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
      ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ) (woodinSparseCompletedAutomorphism θ c f) := by
  rw [(woodinSparseStageCode_inverse h0 hlim hn).1, (woodinSparseStageCode_inverse h0 hlim hn).2]
  exact woodinSparseCompletedAutomorphism_automorphism hΩ hAC hθ h0 hlim hn hf hft

omit hf hft in
theorem woodinSparseCompletedInverse_base_mem {p : V} (hp : p ∈ P) : p ∈ C := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have ht := (woodinSparseStageCode_valid hΩ hAC hsub).system.tops.top θ (mem_succ_self θ)
  rw [woodinSparseStageCode_top hΩ hAC hsub] at ht
  have hz := ht.1
  rw [(woodinSparseStageCode_inverse h0 hlim hn).1] at hz
  have hw := (mem_sparsePairCarrier_iff.mp hz).2.2
  rw [value_eq_empty_of_not_mem_domain (by rw [domain_empty]; exact not_mem_empty)] at hw
  have hsp := (woodinSparseCompletedAutomorphism_inputs hΩ hAC hθ h0 hlim hn).2.2.2.2
  have hh := sparseAppend_mem_pairCarrier hsp hp hw
  rwa [sparseAppend_empty] at hh

theorem woodinSparseCompletedAutomorphism_base_section {p : V} (hp : p ∈ P) :
    p ∈ C ∧ (woodinSparseCompletedAutomorphism θ c f) ‘ p = f ‘ p := by
  have hmem := woodinSparseCompletedInverse_base_mem hΩ hAC hθ h0 hlim hn hp
  have hs := (woodinSparseCompletedAutomorphism_inputs hΩ hAC hθ h0 hlim hn).2.2.2.2 p hp
  let := hs.1
  refine ⟨hmem, ?_⟩
  have hv : p ‘ θ = ∅ := value_eq_empty_of_not_mem_domain (fun hh ↦ mem_irrefl θ (hs.2.1 θ hh))
  rw [woodinSparseCompletedAutomorphism_empty_tail hΩ hAC hθ h0 hlim hn hf hft hmem hv,
    IsFunction.restrict_eq_self p θ hs.2.1]

end ZFVP
