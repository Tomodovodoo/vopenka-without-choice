import ZFVP.ModelTheory.WoodinActualDirectMaps
import ZFVP.ModelTheory.WoodinRecodedDirectNext
import ZFVP.ModelTheory.WoodinNormalizedEndpoint

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinNormalizedStage_through_endpoint {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    IsForcingIterationCode (succ θ) (woodinNormalizedStageCode θ) ∧
      ForcingCodeExtends (woodinNormalizedPrefixCode θ) (woodinNormalizedStageCode θ) := by
  let := hΩ.inaccessible.1
  rcases IsOrdinal.subset_iff.mp hθ with rfl | hθ
  · exact ⟨woodinNormalizedStageCode_endpoint_valid hΩ hAC, woodinNormalizedStageCode_endpoint_extends hΩ hAC⟩
  · exact ⟨woodinNormalizedStageCode_valid hΩ hAC hθ, woodinNormalizedStage_extends hΩ hAC hθ⟩

variable {Ω θ Q T m : V} [IsOrdinal θ]
local notation "N" => woodinNormalizedPrefixCode θ
local notation "C" => woodinNormalizedStageCode θ
local notation "c" => forcingRecodedCode θ N Q T m
local notation "U" => forcingCodeUniverse (woodinIterationPrefix θ)
local notation "A" => forcingSparseCodes θ c (forcingCodeUniverse c)
local notation "B" => forcingSparseOrder θ c (forcingCodeUniverse c)
local notation "f" => woodinRecodedDirectMap θ c m

theorem woodinRecodedDirectMap_lift {i z p : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP N) ‘ i) ((forcingCodeR N) ‘ i)
      (Q ‘ i) (T ‘ i) (m ‘ i))
    (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
    (hQt : IsIterationTable θ Q) (hTt : IsIterationTable θ T)
    (hi : i ∈ θ) (hz : z ∈ (forcingCodeP C) ‘ θ) (hp : p ∈ (forcingCodeP N) ‘ i)
    (hle : ⟨p, ((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ) ‘ z⟩ₖ ∈ (forcingCodeR C) ‘ i) :
    f ‘ (((forcingCodeL C) ‘ ⟨i, θ⟩ₖ) ‘ ⟨z, p⟩ₖ) =
      (forcingSparseEncode θ c (forcingCodeUniverse c)) ‘
        (forcingThreadSplice θ (forcingCodeπ c) (forcingCodeL c)
          ((forcingSparseDecode θ c (forcingCodeUniverse c)) ‘ (f ‘ z)) i ((m ‘ i) ‘ p)) := by
  have hN := woodinNormalizedPrefixCode_valid hΩ hAC hθ
  obtain ⟨hC, he⟩ := woodinNormalizedStage_through_endpoint hΩ hAC hθ
  have hU := woodinNormalizedPrefix_subset_universe hΩ hAC hθ
  have hpC : p ∈ (forcingCodeP C) ‘ i := by
    rwa [← hN.tableP.value_of_subset hC.tableP he.subP hi]
  have hl := (hC.system.lifts.lift i (mem_succ_iff.mpr (Or.inr hi)) θ (mem_succ_self θ)
    (IsOrdinal.toIsTransitive.transitive _ hi) z hz p hpC hle).1
  have hzD := hz
  have hlD := hl
  rw [(woodinNormalized_direct_dictionary hΩ hAC hθ h0 hlim hinac).1] at hzD hlD
  have hv := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp (forcingDirectLimit_subset _ _ _ _ _ _ hzD)).2.1
  have ht := forcingRecoded_threadSplice hN hm hi hp hv
  rw [woodinRecodedDirectMap, forcingRecodedSparseMap_value hN hm hT hQt hTt hU hlD,
    forcingRecodedSparseMap_decode hN hm hT hQt hTt hU hzD,
    woodinNormalizedStage_direct_lift hΩ hAC hθ h0 hlim hinac hi hz hp]
  apply congrArg (fun x : V ↦ (forcingSparseEncode θ c (forcingCodeUniverse c)) ‘ x)
  simpa only [forcingRecodedCode, forcingCodeπ_code, forcingCodeL_code] using ht

local notation "next" => woodinRecodedDirectNextCode θ Q T m

theorem woodinRecodedDirectNext_lift {i q b : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP N) ‘ i) ((forcingCodeR N) ‘ i)
      (Q ‘ i) (T ‘ i) (m ‘ i))
    (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
    (hQt : IsIterationTable θ Q) (hTt : IsIterationTable θ T)
    (hi : i ∈ θ) (hq : q ∈ A) (hb : b ∈ Q ‘ i)
    (hle : ⟨b, ((forcingCodeπ next) ‘ ⟨i, θ⟩ₖ) ‘ q⟩ₖ ∈ T ‘ i) :
    ((forcingCodeL next) ‘ ⟨i, θ⟩ₖ) ‘ ⟨q, b⟩ₖ =
      (forcingSparseEncode θ c (forcingCodeUniverse c)) ‘
        (forcingThreadSplice θ (forcingCodeπ c) (forcingCodeL c)
          ((forcingSparseDecode θ c (forcingCodeUniverse c)) ‘ q) i b) := by
  have hN := woodinNormalizedPrefixCode_valid hΩ hAC hθ
  obtain ⟨hC, he⟩ := woodinNormalizedStage_through_endpoint hΩ hAC hθ
  have hf := woodinRecodedDirectMap_isomorphism hΩ hAC hθ h0 hlim hinac hm hT hQt hTt
  have hm' := forcingRecoded_next_family
    (fun _ hi ↦ (hN.tableP.value_of_subset hC.tableP he.subP hi).symm)
    (fun _ hi ↦ (hN.tableR.value_of_subset hC.tableR he.subR hi).symm) hm hf
  obtain ⟨z, hz, rfl⟩ := hf.surjective q hq
  obtain ⟨p, hp, rfl⟩ := (hm i hi).surjective b hb
  have hpC : p ∈ (forcingCodeP C) ‘ i := by
    rwa [← hN.tableP.value_of_subset hC.tableP he.subP hi]
  have hi' : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
  have hij : i ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hi
  have hmi : IsForcingIsomorphism ((forcingCodeP C) ‘ i) ((forcingCodeR C) ‘ i) (Q ‘ i) (T ‘ i) (m ‘ i) := by
    simpa only [forcingFamilyNext_old hi] using hm' i hi'
  have hproj := forcingRecodedProjections_image hC hm' hi' (mem_succ_self θ) hij hz
  have hproj' : ((forcingCodeπ next) ‘ ⟨i, θ⟩ₖ) ‘ (f ‘ z) =
      (m ‘ i) ‘ (((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ) ‘ z) := by
    simpa only [woodinRecodedDirectNextCode, forcingRecodedCode, forcingCodeπ_code,
      forcingFamilyNext_new, forcingFamilyNext_old hi] using hproj
  rw [hproj', ← hmi.2.2.2 p hpC _ (hC.system.split.projMaps i hi' θ (mem_succ_self θ) hij z hz)] at hle
  have hnew := forcingRecodedLifts_image hm' hi' (mem_succ_self θ) hz hpC
  have hnew' : ((forcingCodeL next) ‘ ⟨i, θ⟩ₖ) ‘ ⟨f ‘ z, (m ‘ i) ‘ p⟩ₖ =
      f ‘ (((forcingCodeL C) ‘ ⟨i, θ⟩ₖ) ‘ ⟨z, p⟩ₖ) := by
    simpa only [woodinRecodedDirectNextCode, forcingRecodedCode, forcingCodeL_code,
      forcingFamilyNext_new, forcingFamilyNext_old hi] using hnew
  rw [hnew']
  exact woodinRecodedDirectMap_lift hΩ hAC hθ h0 hlim hinac hm hT hQt hTt hi hz hp hle

end ZFVP
