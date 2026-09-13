import ZFVP.ModelTheory.NameTwoStepOrderDefinability
import ZFVP.ModelTheory.WoodinRecodedInverseCoherence
import ZFVP.ModelTheory.ForcingRecodedExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinRecodedInverseCarrier (θ c : V) : V :=
  let A := forcingInverseCodePoset θ c
  let B := forcingInverseCodeOrder θ c
  let top := forcingInverseCodeTop θ c
  let γ := woodinLimitCardinal (woodinIterationCardinalPrefix θ)
  let δ := forcingInverseSourceCutoff θ c γ
  normalizedNameTwoStep A B top δ (saturatedHartogsPosetName A B top γ δ)

noncomputable def woodinRecodedInverseOrder (θ c : V) : V :=
  let A := forcingInverseCodePoset θ c
  let B := forcingInverseCodeOrder θ c
  let top := forcingInverseCodeTop θ c
  let γ := woodinLimitCardinal (woodinIterationCardinalPrefix θ)
  let δ := forcingInverseSourceCutoff θ c γ
  nameTwoStepOrderOn A B (saturatedHartogsOrderName A B top γ δ) (woodinRecodedInverseCarrier θ c)

noncomputable def woodinRecodedInverseNextCode (θ Q T m : V) : V :=
  let c := forcingRecodedCode θ (woodinNormalizedPrefixCode θ) Q T m
  forcingRecodedCode (succ θ) (woodinNormalizedStageCode θ)
    (forcingFamilyNext θ Q (woodinRecodedInverseCarrier θ c))
    (forcingFamilyNext θ T (woodinRecodedInverseOrder θ c))
    (forcingFamilyNext θ m (woodinRecodedInverseMap θ c m))

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

instance woodinRecodedInverseCarrier_definable : ℒₛₑₜ-function₂[V] woodinRecodedInverseCarrier := by
  unfold woodinRecodedInverseCarrier
  dsimp only
  apply Language.DefinableFunction₅.comp <;> definability

instance woodinRecodedInverseOrder_definable : ℒₛₑₜ-function₂[V] woodinRecodedInverseOrder := by
  unfold woodinRecodedInverseOrder
  dsimp only
  apply Language.DefinableFunction₄.comp <;> definability

instance woodinRecodedInverseNextCode_definable : ℒₛₑₜ-function₄[V] woodinRecodedInverseNextCode := by
  unfold woodinRecodedInverseNextCode
  dsimp only
  apply Language.DefinableFunction₅.comp <;> definability

variable {Ω θ Q T m : V} [IsOrdinal θ]
local notation "N" => woodinNormalizedPrefixCode θ
local notation "C" => woodinNormalizedStageCode θ
local notation "c" => forcingRecodedCode θ N Q T m
local notation "A" => woodinRecodedInverseCarrier θ c
local notation "B" => woodinRecodedInverseOrder θ c
local notation "f" => woodinRecodedInverseMap θ c m
local notation "next" => woodinRecodedInverseNextCode θ Q T m
local notation "nextm" => forcingFamilyNext θ m f

variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
variable (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
variable (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
variable (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP (woodinNormalizedPrefixCode θ)) ‘ i)
  ((forcingCodeR (woodinNormalizedPrefixCode θ)) ‘ i) (Q ‘ i) (T ‘ i) (m ‘ i))
variable (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
variable (hQt : IsIterationTable θ Q) (hTt : IsIterationTable θ T)
variable (hQrank : ∀ i ∈ θ, Q ‘ i ∈ hierarchy (woodinNormalizedInverseCutoff θ))

include hΩ hAC hθ h0 hlim hn hm hT hQt hTt hQrank

theorem woodinRecodedInverseNext_family :
    ∀ i ∈ succ θ, IsForcingIsomorphism ((forcingCodeP C) ‘ i) ((forcingCodeR C) ‘ i)
      ((forcingFamilyNext θ Q A) ‘ i) ((forcingFamilyNext θ T B) ‘ i) (nextm ‘ i) := by
  apply forcingRecoded_next_family
    (fun _ hi ↦ woodinNormalizedStage_inverse_old_carrier h0 hlim hn hi)
    (fun _ hi ↦ woodinNormalizedStage_inverse_old_order h0 hlim hn hi) hm
  exact woodinRecodedInverseMap_isomorphism hΩ hAC hθ h0 hlim hn hm hT hQt hTt hQrank

theorem woodinRecodedInverseNext_valid : IsForcingIterationCode (succ θ) next := by
  apply forcingRecoded_next_code (woodinNormalizedStageCode_valid hΩ hAC hθ)
    (fun _ hi ↦ woodinNormalizedStage_inverse_old_carrier h0 hlim hn hi)
    (fun _ hi ↦ woodinNormalizedStage_inverse_old_order h0 hlim hn hi) hm hT
    (woodinRecodedInverseMap_isomorphism hΩ hAC hθ h0 hlim hn hm hT hQt hTt hQrank)
  exact sep_subset

omit hΩ hAC hθ h0 hlim hn hm hT hQt hTt hQrank [IsOrdinal θ] in
theorem woodinRecodedInverseNext_carrier_order :
    (forcingCodeP next) ‘ θ = A ∧ (forcingCodeR next) ‘ θ = B := by
  simp only [woodinRecodedInverseNextCode, forcingRecodedCode, forcingCodeP_code,
    forcingCodeR_code, forcingFamilyNext_new, and_self]

omit hQrank in
theorem woodinRecodedInverseNext_top :
    (forcingCodet next) ‘ θ = ⟨forcingInverseCodeTop θ c, ∅⟩ₖ := by
  simp only [woodinRecodedInverseNextCode, forcingRecodedCode, forcingCodet_code,
    forcingRecodedTops_value (mem_succ_self θ), forcingFamilyNext_new]
  exact woodinRecodedInverseMap_top hΩ hAC hθ h0 hlim hn hm hT hQt hTt

theorem woodinRecodedInverseNext_projection {i q : V} (hi : i ∈ θ) (hq : q ∈ A) :
    ((forcingCodeπ next) ‘ ⟨i, θ⟩ₖ) ‘ q = (kpair.π₁ q) ‘ i := by
  have hf := woodinRecodedInverseMap_isomorphism hΩ hAC hθ h0 hlim hn hm hT hQt hTt hQrank
  obtain ⟨z, hz, rfl⟩ := hf.surjective q hq
  have hm' := woodinRecodedInverseNext_family hΩ hAC hθ h0 hlim hn hm hT hQt hTt hQrank
  have he := forcingRecodedProjections_image (woodinNormalizedStageCode_valid hΩ hAC hθ) hm'
    (mem_succ_iff.mpr (Or.inr hi)) (mem_succ_self θ) (IsOrdinal.toIsTransitive.transitive _ hi) hz
  simp only [forcingFamilyNext_new, forcingFamilyNext_old hi] at he
  rw [woodinRecodedInverseNextCode, forcingRecodedCode, forcingCodeπ_code]
  rw [he]
  exact (woodinRecodedInverseMap_projection hΩ hAC hθ h0 hlim hn hi hz).symm

theorem woodinRecodedInverseNext_section {i q : V} (hi : i ∈ θ) (hq : q ∈ Q ‘ i) :
    ((forcingCodeE next) ‘ ⟨i, θ⟩ₖ) ‘ q =
      ⟨forcingSectionThread θ (forcingCodeπ c) (forcingCodeE c) i q, ∅⟩ₖ := by
  obtain ⟨p, hp, rfl⟩ := (hm i hi).surjective q hq
  have hpC : p ∈ (forcingCodeP C) ‘ i := (woodinNormalizedStage_inverse_old_carrier h0 hlim hn hi).symm ▸ hp
  have hm' := woodinRecodedInverseNext_family hΩ hAC hθ h0 hlim hn hm hT hQt hTt hQrank
  have he := forcingRecodedSections_image (woodinNormalizedStageCode_valid hΩ hAC hθ) hm'
    (mem_succ_iff.mpr (Or.inr hi)) (mem_succ_self θ) (IsOrdinal.toIsTransitive.transitive _ hi) hpC
  simp only [forcingFamilyNext_new, forcingFamilyNext_old hi] at he
  rw [woodinRecodedInverseNextCode, forcingRecodedCode, forcingCodeE_code]
  rw [he]
  exact woodinRecodedInverseMap_section hΩ hAC hθ h0 hlim hn hm hT hQt hTt hi hp

end ZFVP
