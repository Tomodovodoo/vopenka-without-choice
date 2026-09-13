import ZFVP.ModelTheory.WoodinRecodedInverseNext
import ZFVP.ModelTheory.ForcingThreadSpliceTransport

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ Q T m : V} [IsOrdinal θ]
local notation "N" => woodinNormalizedPrefixCode θ
local notation "C" => woodinNormalizedStageCode θ
local notation "c" => forcingRecodedCode θ N Q T m
local notation "γ" => woodinLimitCardinal (woodinIterationCardinalPrefix θ)

theorem woodinRecodedInverseMap_lift {i z p : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ)) (hn : ¬IsChoicelessInaccessible γ)
    (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP N) ‘ i) ((forcingCodeR N) ‘ i)
      (Q ‘ i) (T ‘ i) (m ‘ i))
    (hi : i ∈ θ) (hz : z ∈ (forcingCodeP C) ‘ θ) (hp : p ∈ (forcingCodeP N) ‘ i)
    (hle : ⟨p, ((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ) ‘ z⟩ₖ ∈ (forcingCodeR C) ‘ i) :
    (woodinRecodedInverseMap θ c m) ‘ (((forcingCodeL C) ‘ ⟨i, θ⟩ₖ) ‘ ⟨z, p⟩ₖ) =
      ⟨forcingThreadSplice θ (forcingCodeπ c) (forcingCodeL c)
          (kpair.π₁ ((woodinRecodedInverseMap θ c m) ‘ z)) i ((m ‘ i) ‘ p),
        kpair.π₂ ((woodinRecodedInverseMap θ c m) ‘ z)⟩ₖ := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hS := (woodinIterationPrefix_of_stages
    (fun j hj ↦ ((woodinIterationExit hΩ hAC).2.1 j (hsub j hj)).1)).code
  have hN := woodinNormalizedPrefixCode_valid hΩ hAC hsub
  have hM := woodinNormalizationHistory_actual_prefix hΩ hAC hsub
  have hpC : p ∈ (forcingCodeP C) ‘ i := (woodinNormalizedStage_inverse_old_carrier h0 hlim hn hi).symm ▸ hp
  have hl := ((woodinNormalizedStageCode_valid hΩ hAC hθ).system.lifts.lift
    i (mem_succ_iff.mpr (Or.inr hi)) θ (mem_succ_self θ)
    (IsOrdinal.toIsTransitive.transitive _ hi) z hz p hpC hle).1
  have hbase : kpair.π₁ z ∈ woodinNormalizedInverseBase θ := by
    have hz' := hz
    rw [(woodinNormalized_inverse_dictionary hΩ hAC hθ h0 hlim hn).1] at hz'
    obtain ⟨a, ha, τ, _, rfl⟩ := mem_prod_iff.mp hz'
    simpa only [kpair.π₁_kpair] using ha
  have hsplice : forcingThreadSplice θ (forcingCodeπ (woodinIterationPrefix θ))
      (forcingCodeL (woodinIterationPrefix θ)) (kpair.π₁ z) i p ∈ woodinNormalizedInverseBase θ := by
    have hl' := hl
    rw [woodinNormalizedStage_inverse_lift hΩ hAC hθ h0 hlim hn hi hz hp,
      (woodinNormalized_inverse_dictionary hΩ hAC hθ h0 hlim hn).1] at hl'
    exact (kpair_mem_iff.mp hl').1
  have hv : ∀ j ∈ θ, (kpair.π₁ z) ‘ j ∈ (forcingCodeP N) ‘ j :=
    ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hbase).2.1
  have hpN : p ∈ (forcingNormalizationCarriers θ (woodinIterationPrefix θ)
      (woodinNormalizationHistory θ)) ‘ i := by
    simpa only [woodinNormalizedPrefixCode, forcingNormalizedCode, forcingCodeP_code] using hp
  have hvN : ∀ j ∈ θ, (kpair.π₁ z) ‘ j ∈ (forcingNormalizationCarriers θ (woodinIterationPrefix θ)
      (woodinNormalizationHistory θ)) ‘ j := by
    simpa only [woodinNormalizedPrefixCode, forcingNormalizedCode, forcingCodeP_code] using hv
  have hnorm := forcingNormalized_threadSplice hS hM hi hpN hvN
  have hrec := forcingRecoded_threadSplice hN hm hi hp hv
  rw [woodinRecodedInverseMap_value hΩ hAC hθ h0 hlim hn hl,
    woodinNormalizedStage_inverse_lift hΩ hAC hθ h0 hlim hn hi hz hp,
    woodinRecodedInverseMap_value hΩ hAC hθ h0 hlim hn hz]
  simp only [normalizedTwoStepIsoValue, kpair.π₁_kpair, kpair.π₂_kpair]
  rw [woodinRecodedInverseBaseMap, forcingThreadActionMap_value hsplice, forcingThreadActionMap_value hbase]
  apply congrArg (fun x : V ↦ ⟨x, _⟩ₖ)
  rw [← hnorm]
  simpa only [woodinNormalizedPrefixCode, forcingNormalizedCode, forcingCodeπ_code,
    forcingCodeL_code, forcingRecodedCode] using hrec

local notation "next" => woodinRecodedInverseNextCode θ Q T m

theorem woodinRecodedInverseNext_lift {i q b : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ)) (hn : ¬IsChoicelessInaccessible γ)
    (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP N) ‘ i) ((forcingCodeR N) ‘ i)
      (Q ‘ i) (T ‘ i) (m ‘ i))
    (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
    (hQt : IsIterationTable θ Q) (hTt : IsIterationTable θ T)
    (hQrank : ∀ i ∈ θ, Q ‘ i ∈ hierarchy (woodinNormalizedInverseCutoff θ))
    (hi : i ∈ θ) (hq : q ∈ woodinRecodedInverseCarrier θ c) (hb : b ∈ Q ‘ i)
    (hle : ⟨b, ((forcingCodeπ next) ‘ ⟨i, θ⟩ₖ) ‘ q⟩ₖ ∈ T ‘ i) :
    ((forcingCodeL next) ‘ ⟨i, θ⟩ₖ) ‘ ⟨q, b⟩ₖ =
      ⟨forcingThreadSplice θ (forcingCodeπ c) (forcingCodeL c) (kpair.π₁ q) i b, kpair.π₂ q⟩ₖ := by
  have hC := woodinNormalizedStageCode_valid hΩ hAC hθ
  have hf := woodinRecodedInverseMap_isomorphism hΩ hAC hθ h0 hlim hn hm hT hQt hTt hQrank
  obtain ⟨z, hz, rfl⟩ := hf.surjective q hq
  obtain ⟨p, hp, rfl⟩ := (hm i hi).surjective b hb
  have hpC : p ∈ (forcingCodeP C) ‘ i := (woodinNormalizedStage_inverse_old_carrier h0 hlim hn hi).symm ▸ hp
  have hi' : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
  have hij : i ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hi
  have hm' := woodinRecodedInverseNext_family hΩ hAC hθ h0 hlim hn hm hT hQt hTt hQrank
  have hmi : IsForcingIsomorphism ((forcingCodeP C) ‘ i) ((forcingCodeR C) ‘ i) (Q ‘ i) (T ‘ i) (m ‘ i) := by
    simpa only [forcingFamilyNext_old hi] using hm' i hi'
  have hproj := forcingRecodedProjections_image hC hm' hi' (mem_succ_self θ) hij hz
  have hproj' : ((forcingCodeπ next) ‘ ⟨i, θ⟩ₖ) ‘ ((woodinRecodedInverseMap θ c m) ‘ z) =
      (m ‘ i) ‘ (((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ) ‘ z) := by
    simpa only [woodinRecodedInverseNextCode, forcingRecodedCode, forcingCodeπ_code,
      forcingFamilyNext_new, forcingFamilyNext_old hi] using hproj
  rw [hproj', ← hmi.2.2.2 p hpC _ (hC.system.split.projMaps i hi' θ (mem_succ_self θ) hij z hz)] at hle
  have hnew := forcingRecodedLifts_image hm' hi' (mem_succ_self θ) hz hpC
  have hnew' : ((forcingCodeL next) ‘ ⟨i, θ⟩ₖ) ‘
      ⟨(woodinRecodedInverseMap θ c m) ‘ z, (m ‘ i) ‘ p⟩ₖ =
      (woodinRecodedInverseMap θ c m) ‘ (((forcingCodeL C) ‘ ⟨i, θ⟩ₖ) ‘ ⟨z, p⟩ₖ) := by
    simpa only [woodinRecodedInverseNextCode, forcingRecodedCode, forcingCodeL_code,
      forcingFamilyNext_new, forcingFamilyNext_old hi] using hnew
  rw [hnew']
  exact woodinRecodedInverseMap_lift hΩ hAC hθ h0 hlim hn hm hi hz hp hle

end ZFVP
