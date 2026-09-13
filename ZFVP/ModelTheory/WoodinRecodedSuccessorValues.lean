import ZFVP.ModelTheory.WoodinRecodedSuccessorNext
import ZFVP.ModelTheory.WoodinActualSuccessorMaps

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω k c m z : V} [IsOrdinal k]
local notation "C" => woodinNormalizedStageCode (succ k)
local notation "A" => (forcingCodeP c) ‘ k
local notation "B" => (forcingCodeR c) ‘ k
local notation "top" => (forcingCodet c) ‘ k

theorem woodinRecodedSuccessorMap_value
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : k ∈ Ω)
    (hz : z ∈ (forcingCodeP C) ‘ (succ k)) :
    (woodinRecodedSuccessorMap k c m) ‘ z = normalizedTwoStepIsoValue A B top (m ‘ k) z := by
  rw [(woodinNormalizedStage_successor_eq hΩ hAC hk).1] at hz
  exact normalizedTwoStepIsoMap_value hz

theorem woodinRecodedSuccessorMap_prefix
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : k ∈ Ω)
    (hz : z ∈ (forcingCodeP C) ‘ (succ k)) :
    kpair.π₁ ((woodinRecodedSuccessorMap k c m) ‘ z) = (m ‘ k) ‘ (kpair.π₁ z) := by
  rw [woodinRecodedSuccessorMap_value hΩ hAC hk hz, normalizedTwoStepIsoValue_prefix]

theorem woodinRecodedSuccessorMap_empty_tail {p : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : k ∈ Ω)
    (hc : IsForcingIterationCode (succ k) c)
    (hp : ⟨p, ∅⟩ₖ ∈ (forcingCodeP C) ‘ (succ k)) :
    (woodinRecodedSuccessorMap k c m) ‘ ⟨p, ∅⟩ₖ = ⟨(m ‘ k) ‘ p, ∅⟩ₖ := by
  rw [woodinRecodedSuccessorMap_value hΩ hAC hk hp]
  exact normalizedTwoStepIsoValue_empty_tail (hc.system.order.preorder k (mem_succ_self k))
    (hc.system.tops.top k (mem_succ_self k)).1

theorem woodinRecodedSuccessorMap_section {i p : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : succ k ∈ Ω)
    (hc : IsForcingIterationCode (succ k) c) (hi : i ∈ succ k)
    (hp : p ∈ (forcingCodeP (woodinNormalizedStageCode k)) ‘ i) :
    (woodinRecodedSuccessorMap k c m) ‘ (((forcingCodeE C) ‘ ⟨i, succ k⟩ₖ) ‘ p) =
      ⟨(m ‘ k) ‘ (((forcingCodeE (woodinNormalizedStageCode k)) ‘ ⟨i, k⟩ₖ) ‘ p), ∅⟩ₖ := by
  let := hΩ.inaccessible.1
  have hk0 := IsOrdinal.toIsTransitive.mem_trans (mem_succ_self k) hk
  have hpC : p ∈ (forcingCodeP C) ‘ i :=
    (woodinNormalizedStage_successor_old_carrier hΩ hAC hk0 hi).symm ▸ hp
  have hz := (woodinNormalizedStageCode_valid hΩ hAC hk).system.split.secMaps
    i (mem_succ_iff.mpr (Or.inr hi)) (succ k) (mem_succ_self (succ k))
    (IsOrdinal.toIsTransitive.transitive _ hi) p hpC
  rw [woodinNormalizedStage_successor_section hΩ hAC hk0 hi hp] at hz ⊢
  exact woodinRecodedSuccessorMap_empty_tail hΩ hAC hk0 hc hz

variable {Q T : V}
local notation "N" => woodinNormalizedPrefixCode (succ k)
local notation "r" => forcingRecodedCode (succ k) N Q T m
local notation "next" => woodinRecodedSuccessorNextCode k Q T m

variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : succ k ∈ Ω)
variable (hm : ∀ i ∈ succ k, IsForcingIsomorphism
  ((forcingCodeP (woodinNormalizedPrefixCode (succ k))) ‘ i)
  ((forcingCodeR (woodinNormalizedPrefixCode (succ k))) ‘ i) (Q ‘ i) (T ‘ i) (m ‘ i))
variable (hT : ∀ i ∈ succ k, IsForcingPreorder (Q ‘ i) (T ‘ i))
variable (hQt : IsIterationTable (succ k) Q) (hTt : IsIterationTable (succ k) T)
variable (hQrank : Q ‘ k ∈ hierarchy (woodinNormalizedSuccessorCutoff k))

include hΩ hAC hk hm hT hQt hTt hQrank

theorem woodinRecodedSuccessorNext_section {i q : V} (hi : i ∈ succ k) (hq : q ∈ Q ‘ i) :
    ((forcingCodeE next) ‘ ⟨i, succ k⟩ₖ) ‘ q = ⟨((forcingCodeE r) ‘ ⟨i, k⟩ₖ) ‘ q, ∅⟩ₖ := by
  let := hΩ.inaccessible.1
  have hk0 := IsOrdinal.toIsTransitive.mem_trans (mem_succ_self k) hk
  have hs := woodinNormalizedPrefixCode_valid hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hk)
  have hr := forcingRecoded_code hs hm hT hQt hTt
  obtain ⟨p, hp, rfl⟩ := (hm i hi).surjective q hq
  have hp0 : p ∈ (forcingCodeP (woodinNormalizedStageCode k)) ‘ i := by
    rwa [woodinNormalizedPrefix_successor hΩ hAC hk0] at hp
  have hpC : p ∈ (forcingCodeP C) ‘ i :=
    (woodinNormalizedStage_successor_old_carrier hΩ hAC hk0 hi).symm ▸ hp0
  have hnew := forcingRecodedSections_image (woodinNormalizedStageCode_valid hΩ hAC hk)
    (woodinRecodedSuccessorNext_family hΩ hAC hk hm hT hQt hTt hQrank)
    (mem_succ_iff.mpr (Or.inr hi)) (mem_succ_self (succ k))
    (IsOrdinal.toIsTransitive.transitive _ hi) hpC
  simp only [forcingFamilyNext_new, forcingFamilyNext_old hi] at hnew
  have hik : i ⊆ k := by
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact subset_refl _
    · exact IsOrdinal.toIsTransitive.transitive _ hi
  have hold := forcingRecodedSections_image hs hm hi (mem_succ_self k) hik hp
  rw [woodinNormalizedPrefix_successor hΩ hAC hk0] at hold
  have hnew' : ((forcingCodeE next) ‘ ⟨i, succ k⟩ₖ) ‘ ((m ‘ i) ‘ p) =
      (woodinRecodedSuccessorMap k r m) ‘ (((forcingCodeE C) ‘ ⟨i, succ k⟩ₖ) ‘ p) := by
    simpa only [woodinRecodedSuccessorNextCode, forcingRecodedCode, forcingCodeE_code] using hnew
  rw [hnew', woodinRecodedSuccessorMap_section hΩ hAC hk hr hi hp0]
  have hold' : ((forcingCodeE r) ‘ ⟨i, k⟩ₖ) ‘ ((m ‘ i) ‘ p) =
      (m ‘ k) ‘ (((forcingCodeE (woodinNormalizedStageCode k)) ‘ ⟨i, k⟩ₖ) ‘ p) := by
    simpa only [forcingRecodedCode, forcingCodeE_code, woodinNormalizedPrefix_successor hΩ hAC hk0] using hold
  rw [hold']

theorem woodinRecodedSuccessorNext_projection {i q : V} (hi : i ∈ succ k)
    (hq : q ∈ woodinRecodedSuccessorCarrier k r) :
    ((forcingCodeπ next) ‘ ⟨i, succ k⟩ₖ) ‘ q = ((forcingCodeπ r) ‘ ⟨i, k⟩ₖ) ‘ (kpair.π₁ q) := by
  let := hΩ.inaccessible.1
  have hk0 := IsOrdinal.toIsTransitive.mem_trans (mem_succ_self k) hk
  have hs := woodinNormalizedPrefixCode_valid hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hk)
  have hf := woodinRecodedSuccessorMap_isomorphism hΩ hAC hk0 hm hT hQt hTt hQrank
  obtain ⟨z, hz, rfl⟩ := hf.surjective q hq
  have hnew := forcingRecodedProjections_image (woodinNormalizedStageCode_valid hΩ hAC hk)
    (woodinRecodedSuccessorNext_family hΩ hAC hk hm hT hQt hTt hQrank)
    (mem_succ_iff.mpr (Or.inr hi)) (mem_succ_self (succ k))
    (IsOrdinal.toIsTransitive.transitive _ hi) hz
  simp only [forcingFamilyNext_new, forcingFamilyNext_old hi] at hnew
  have hnew' : ((forcingCodeπ next) ‘ ⟨i, succ k⟩ₖ) ‘ ((woodinRecodedSuccessorMap k r m) ‘ z) =
      (m ‘ i) ‘ (((forcingCodeπ C) ‘ ⟨i, succ k⟩ₖ) ‘ z) := by
    simpa only [woodinRecodedSuccessorNextCode, forcingRecodedCode, forcingCodeπ_code] using hnew
  have hbase : kpair.π₁ z ∈ (forcingCodeP N) ‘ k := by
    have hz' := hz
    rw [(woodinNormalizedStage_successor_eq hΩ hAC hk0).1] at hz'
    obtain ⟨p, hp, τ, _, rfl⟩ := mem_prod_iff.mp hz'
    simpa only [kpair.π₁_kpair, woodinNormalizedPrefix_successor hΩ hAC hk0] using hp
  have hik : i ⊆ k := by
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact subset_refl _
    · exact IsOrdinal.toIsTransitive.transitive _ hi
  have hold := forcingRecodedProjections_image hs hm hi (mem_succ_self k) hik hbase
  have hold' : ((forcingCodeπ r) ‘ ⟨i, k⟩ₖ) ‘ ((m ‘ k) ‘ (kpair.π₁ z)) =
      (m ‘ i) ‘ (((forcingCodeπ (woodinNormalizedStageCode k)) ‘ ⟨i, k⟩ₖ) ‘ (kpair.π₁ z)) := by
    simpa only [forcingRecodedCode, forcingCodeπ_code, woodinNormalizedPrefix_successor hΩ hAC hk0] using hold
  rw [hnew', woodinRecodedSuccessorMap_prefix hΩ hAC hk0 hz,
    woodinNormalizedStage_successor_projection hΩ hAC hk0 hi hz, hold']

end ZFVP
