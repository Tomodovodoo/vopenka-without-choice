import ZFVP.ModelTheory.WoodinActualInverseMaps
import ZFVP.ModelTheory.ForcingSectionThreadTransport
import ZFVP.ModelTheory.WoodinRecodedInverseStage

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ Q T m : V} [IsOrdinal θ]
local notation "S" => woodinIterationPrefix θ
local notation "N" => woodinNormalizedPrefixCode θ
local notation "C" => woodinNormalizedStageCode θ
local notation "c" => forcingRecodedCode θ N Q T m
local notation "γ" => woodinLimitCardinal (woodinIterationCardinalPrefix θ)

theorem woodinNormalizedStage_inverse_section_normalized {i p : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ)) (hn : ¬IsChoicelessInaccessible γ)
    (hi : i ∈ θ) (hp : p ∈ (forcingCodeP N) ‘ i) :
    ((forcingCodeE C) ‘ ⟨i, θ⟩ₖ) ‘ p = ⟨forcingSectionThread θ (forcingCodeπ N) (forcingCodeE N) i p, ∅⟩ₖ := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hx := woodinIterationExit hΩ hAC
  have hs := woodinIterationPrefix_of_stages (fun i hi ↦ (hx.2.1 i (hsub i hi)).1)
  have hm := woodinNormalizationHistory_actual_prefix hΩ hAC hsub
  have hpN : p ∈ (forcingNormalizationCarriers θ S (woodinNormalizationHistory θ)) ‘ i := by
    simpa only [woodinNormalizedPrefixCode, forcingNormalizedCode, forcingCodeP_code] using hp
  rw [woodinNormalizedStage_inverse_section hΩ hAC hθ h0 hlim hn hi hp]
  simp only [woodinNormalizedPrefixCode, forcingNormalizedCode, forcingCodeπ_code, forcingCodeE_code]
  rw [forcingNormalized_sectionThread hs.code hm hi hpN]

theorem woodinRecodedInverseMap_projection {i z : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ)) (hn : ¬IsChoicelessInaccessible γ)
    (hi : i ∈ θ) (hz : z ∈ (forcingCodeP C) ‘ θ) :
    (kpair.π₁ ((woodinRecodedInverseMap θ c m) ‘ z)) ‘ i =
      (m ‘ i) ‘ (((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ) ‘ z) := by
  rw [woodinNormalizedStage_inverse_projection hΩ hAC hθ h0 hlim hn hi hz]
  exact woodinRecodedInverseMap_coordinate hΩ hAC hθ h0 hlim hn hz hi

theorem woodinRecodedInverseMap_section {i p : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ)) (hn : ¬IsChoicelessInaccessible γ)
    (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP N) ‘ i) ((forcingCodeR N) ‘ i)
      (Q ‘ i) (T ‘ i) (m ‘ i))
    (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
    (hQt : IsIterationTable θ Q) (hTt : IsIterationTable θ T)
    (hi : i ∈ θ) (hp : p ∈ (forcingCodeP N) ‘ i) :
    (woodinRecodedInverseMap θ c m) ‘ (((forcingCodeE C) ‘ ⟨i, θ⟩ₖ) ‘ p) =
      ⟨forcingSectionThread θ (forcingCodeπ c) (forcingCodeE c) i ((m ‘ i) ‘ p), ∅⟩ₖ := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hs := woodinNormalizedPrefixCode_valid hΩ hAC hsub
  have hs' := woodinNormalizedStageCode_valid hΩ hAC hθ
  have hpC : p ∈ (forcingCodeP C) ‘ i := (woodinNormalizedStage_inverse_old_carrier h0 hlim hn hi).symm ▸ hp
  have hmem := hs'.system.split.secMaps i (mem_succ_iff.mpr (Or.inr hi)) θ (mem_succ_self θ)
    (IsOrdinal.toIsTransitive.transitive _ hi) p hpC
  have he := woodinNormalizedStage_inverse_section_normalized hΩ hAC hθ h0 hlim hn hi hp
  rw [he] at hmem ⊢
  rw [woodinRecodedInverseMap_empty_tail hΩ hAC hθ h0 hlim hn hm hT hQt hTt hmem]
  have hf : forcingSectionThread θ (forcingCodeπ N) (forcingCodeE N) i p ∈ woodinNormalizedInverseBase θ :=
    forcingDirectLimit_subset _ _ _ _ _ _
      (forcingSectionThread_mem hs.system.split hi hp (woodinNormalizedPrefix_subset_universe hΩ hAC hsub))
  rw [woodinRecodedInverseBaseMap, forcingThreadActionMap_value hf, forcingRecoded_sectionThread hs hm hi hp]
  simp only [forcingRecodedCode, forcingCodeπ_code, forcingCodeE_code]

theorem woodinRecodedInverseMap_top
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ)) (hn : ¬IsChoicelessInaccessible γ)
    (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP N) ‘ i) ((forcingCodeR N) ‘ i)
      (Q ‘ i) (T ‘ i) (m ‘ i))
    (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
    (hQt : IsIterationTable θ Q) (hTt : IsIterationTable θ T) :
    (woodinRecodedInverseMap θ c m) ‘ ((forcingCodet C) ‘ θ) = ⟨forcingInverseCodeTop θ c, ∅⟩ₖ := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have ht := (woodinNormalizedStageCode_valid hΩ hAC hθ).system.tops.top θ (mem_succ_self θ)
  have hmem := ht.1
  rw [woodinNormalizedStage_inverse_top h0 hlim hn] at hmem ⊢
  rw [woodinRecodedInverseMap_empty_tail hΩ hAC hθ h0 hlim hn hm hT hQt hTt hmem,
    woodinRecodedInverseBaseMap_top hΩ hAC hsub hm hT hQt hTt hz]

end ZFVP
