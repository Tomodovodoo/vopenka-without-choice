import ZFVP.ModelTheory.WoodinRecodedSuccessorValues

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω k c m : V} [IsOrdinal k]
local notation "C" => woodinNormalizedStageCode (succ k)
local notation "D" => woodinNormalizedStageCode k

theorem woodinRecodedSuccessorMap_lift {i z p : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : succ k ∈ Ω)
    (hi : i ∈ succ k) (hz : z ∈ (forcingCodeP C) ‘ (succ k))
    (hp : p ∈ (forcingCodeP D) ‘ i)
    (hle : ⟨p, ((forcingCodeπ C) ‘ ⟨i, succ k⟩ₖ) ‘ z⟩ₖ ∈ (forcingCodeR C) ‘ i) :
    (woodinRecodedSuccessorMap k c m) ‘ (((forcingCodeL C) ‘ ⟨i, succ k⟩ₖ) ‘ ⟨z, p⟩ₖ) =
      ⟨(m ‘ k) ‘ (((forcingCodeL D) ‘ ⟨i, k⟩ₖ) ‘ ⟨kpair.π₁ z, p⟩ₖ),
        kpair.π₂ ((woodinRecodedSuccessorMap k c m) ‘ z)⟩ₖ := by
  let := hΩ.inaccessible.1
  have hk0 := IsOrdinal.toIsTransitive.mem_trans (mem_succ_self k) hk
  have hpC : p ∈ (forcingCodeP C) ‘ i :=
    (woodinNormalizedStage_successor_old_carrier hΩ hAC hk0 hi).symm ▸ hp
  have hl := ((woodinNormalizedStageCode_valid hΩ hAC hk).system.lifts.lift
    i (mem_succ_iff.mpr (Or.inr hi)) (succ k) (mem_succ_self (succ k))
    (IsOrdinal.toIsTransitive.transitive _ hi) z hz p hpC hle).1
  rw [woodinRecodedSuccessorMap_value hΩ hAC hk0 hl,
    woodinNormalizedStage_successor_lift hΩ hAC hk0 hi hz hp,
    woodinRecodedSuccessorMap_value hΩ hAC hk0 hz]
  simp only [normalizedTwoStepIsoValue, kpair.π₁_kpair, kpair.π₂_kpair]

variable {Q T : V}
local notation "N" => woodinNormalizedPrefixCode (succ k)
local notation "r" => forcingRecodedCode (succ k) N Q T m
local notation "next" => woodinRecodedSuccessorNextCode k Q T m

theorem woodinRecodedSuccessorNext_lift {i q b : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : succ k ∈ Ω)
    (hm : ∀ i ∈ succ k, IsForcingIsomorphism ((forcingCodeP N) ‘ i) ((forcingCodeR N) ‘ i)
      (Q ‘ i) (T ‘ i) (m ‘ i))
    (hT : ∀ i ∈ succ k, IsForcingPreorder (Q ‘ i) (T ‘ i))
    (hQt : IsIterationTable (succ k) Q) (hTt : IsIterationTable (succ k) T)
    (hQrank : Q ‘ k ∈ hierarchy (woodinNormalizedSuccessorCutoff k))
    (hi : i ∈ succ k) (hq : q ∈ woodinRecodedSuccessorCarrier k r) (hb : b ∈ Q ‘ i)
    (hle : ⟨b, ((forcingCodeπ next) ‘ ⟨i, succ k⟩ₖ) ‘ q⟩ₖ ∈ T ‘ i) :
    ((forcingCodeL next) ‘ ⟨i, succ k⟩ₖ) ‘ ⟨q, b⟩ₖ =
      ⟨((forcingCodeL r) ‘ ⟨i, k⟩ₖ) ‘ ⟨kpair.π₁ q, b⟩ₖ, kpair.π₂ q⟩ₖ := by
  let := hΩ.inaccessible.1
  have hk0 := IsOrdinal.toIsTransitive.mem_trans (mem_succ_self k) hk
  have hs := woodinNormalizedPrefixCode_valid hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hk)
  have hC := woodinNormalizedStageCode_valid hΩ hAC hk
  have hf := woodinRecodedSuccessorMap_isomorphism hΩ hAC hk0 hm hT hQt hTt hQrank
  obtain ⟨z, hz, rfl⟩ := hf.surjective q hq
  obtain ⟨p, hp, rfl⟩ := (hm i hi).surjective b hb
  have hpD : p ∈ (forcingCodeP D) ‘ i := by rwa [woodinNormalizedPrefix_successor hΩ hAC hk0] at hp
  have hpC : p ∈ (forcingCodeP C) ‘ i := (woodinNormalizedStage_successor_old_carrier hΩ hAC hk0 hi).symm ▸ hpD
  have hi' : i ∈ succ (succ k) := mem_succ_iff.mpr (Or.inr hi)
  have hij : i ⊆ succ k := IsOrdinal.toIsTransitive.transitive _ hi
  have hm' := woodinRecodedSuccessorNext_family hΩ hAC hk hm hT hQt hTt hQrank
  have hmi : IsForcingIsomorphism ((forcingCodeP C) ‘ i) ((forcingCodeR C) ‘ i) (Q ‘ i) (T ‘ i) (m ‘ i) := by
    simpa only [forcingFamilyNext_old hi] using hm' i hi'
  have hproj := forcingRecodedProjections_image hC hm' hi' (mem_succ_self (succ k)) hij hz
  have hproj' : ((forcingCodeπ next) ‘ ⟨i, succ k⟩ₖ) ‘ ((woodinRecodedSuccessorMap k r m) ‘ z) =
      (m ‘ i) ‘ (((forcingCodeπ C) ‘ ⟨i, succ k⟩ₖ) ‘ z) := by
    simpa only [woodinRecodedSuccessorNextCode, forcingRecodedCode, forcingCodeπ_code,
      forcingFamilyNext_new, forcingFamilyNext_old hi] using hproj
  rw [hproj', ← hmi.2.2.2 p hpC _ (hC.system.split.projMaps i hi' (succ k)
    (mem_succ_self (succ k)) hij z hz)] at hle
  have hnew := forcingRecodedLifts_image hm' hi' (mem_succ_self (succ k)) hz hpC
  have hnew' : ((forcingCodeL next) ‘ ⟨i, succ k⟩ₖ) ‘
      ⟨(woodinRecodedSuccessorMap k r m) ‘ z, (m ‘ i) ‘ p⟩ₖ =
      (woodinRecodedSuccessorMap k r m) ‘ (((forcingCodeL C) ‘ ⟨i, succ k⟩ₖ) ‘ ⟨z, p⟩ₖ) := by
    simpa only [woodinRecodedSuccessorNextCode, forcingRecodedCode, forcingCodeL_code,
      forcingFamilyNext_new, forcingFamilyNext_old hi] using hnew
  have hbase : kpair.π₁ z ∈ (forcingCodeP N) ‘ k := by
    have hz' := hz
    rw [(woodinNormalizedStage_successor_eq hΩ hAC hk0).1] at hz'
    obtain ⟨a, ha, τ, _, rfl⟩ := mem_prod_iff.mp hz'
    simpa only [kpair.π₁_kpair, woodinNormalizedPrefix_successor hΩ hAC hk0] using ha
  have hold := forcingRecodedLifts_image hm hi (mem_succ_self k) hbase hp
  have hold' : ((forcingCodeL r) ‘ ⟨i, k⟩ₖ) ‘ ⟨(m ‘ k) ‘ (kpair.π₁ z), (m ‘ i) ‘ p⟩ₖ =
      (m ‘ k) ‘ (((forcingCodeL D) ‘ ⟨i, k⟩ₖ) ‘ ⟨kpair.π₁ z, p⟩ₖ) := by
    simpa only [forcingRecodedCode, forcingCodeL_code, woodinNormalizedPrefix_successor hΩ hAC hk0] using hold
  rw [hnew', woodinRecodedSuccessorMap_lift hΩ hAC hk hi hz hpD hle,
    woodinRecodedSuccessorMap_prefix hΩ hAC hk0 hz, hold']

end ZFVP
