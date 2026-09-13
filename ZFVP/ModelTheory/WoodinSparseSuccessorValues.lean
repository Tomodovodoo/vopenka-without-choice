import ZFVP.ModelTheory.WoodinSparseSuccessor
import ZFVP.SetTheory.WoodinSparseBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω k Q T m : V} [IsOrdinal k]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : k ∈ Ω)
variable (hm : ∀ i ∈ succ k, IsForcingIsomorphism
  ((forcingCodeP (woodinNormalizedPrefixCode (succ k))) ‘ i)
  ((forcingCodeR (woodinNormalizedPrefixCode (succ k))) ‘ i) (Q ‘ i) (T ‘ i) (m ‘ i))
variable (hT : ∀ i ∈ succ k, IsForcingPreorder (Q ‘ i) (T ‘ i))
variable (hQt : IsIterationTable (succ k) Q) (hTt : IsIterationTable (succ k) T)
variable (hQrank : Q ‘ k ∈ hierarchy (woodinNormalizedSuccessorCutoff k))
variable (hsp : ∀ p ∈ Q ‘ k, IsSparseFunctionOn (woodinSourceIndex (succ k)) p)

local notation "c" => forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m
local notation "C" => woodinNormalizedStageCode (succ k)
local notation "D" => woodinNormalizedStageCode k

include hΩ hAC hk hm hT hQt hTt hQrank hsp

omit hsp in
theorem woodinSparseSuccessorMap_base_mem {z : V} (hz : z ∈ (forcingCodeP C) ‘ (succ k)) :
    (m ‘ k) ‘ (kpair.π₁ z) ∈ Q ‘ k := by
  have hf := woodinRecodedSuccessorMap_isomorphism (Q := Q) (T := T) (m := m) hΩ hAC hk hm hT hQt hTt hQrank
  have hmem := function_value_mem hf.1 hz
  rw [woodinRecodedSuccessorMap_value hΩ hAC hk hz] at hmem
  simpa only [forcingRecodedCode, forcingCodeP_code] using (kpair_mem_iff.mp hmem).1

theorem woodinSparseSuccessorMap_restrict {z : V} (hz : z ∈ (forcingCodeP C) ‘ (succ k)) :
    ((woodinSparseSuccessorMap k c m) ‘ z) ↾ (woodinSourceIndex (succ k)) = (m ‘ k) ‘ (kpair.π₁ z) := by
  have hs := hsp _ (woodinSparseSuccessorMap_base_mem hΩ hAC hk hm hT hQt hTt hQrank hz)
  let := hs.1
  rw [woodinSparseSuccessorMap_value hΩ hAC hk hm hT hQt hTt hQrank hsp hz]
  exact sparseAppend_restrict hs.2.1

theorem woodinSparseSuccessorMap_tail {z : V} (hz : z ∈ (forcingCodeP C) ‘ (succ k)) :
    ((woodinSparseSuccessorMap k c m) ‘ z) ‘ (woodinSourceIndex (succ k)) =
      normalizedIsomorphismName ((forcingCodeP c) ‘ k) ((forcingCodeR c) ‘ k) ((forcingCodet c) ‘ k)
        (m ‘ k) (kpair.π₂ z) := by
  have hs := hsp _ (woodinSparseSuccessorMap_base_mem hΩ hAC hk hm hT hQt hTt hQrank hz)
  let := hs.1
  rw [woodinSparseSuccessorMap_value hΩ hAC hk hm hT hQt hTt hQrank hsp hz]
  exact sparseAppend_value_new hs.2.1

theorem woodinSparseSuccessorMap_empty_tail {p : V} (hp : ⟨p, ∅⟩ₖ ∈ (forcingCodeP C) ‘ (succ k)) :
    (woodinSparseSuccessorMap k c m) ‘ ⟨p, ∅⟩ₖ = (m ‘ k) ‘ p := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ (hΩ.inaccessible.rankCriterion.2.2.1 k hk)
  have hc := forcingRecoded_code (woodinNormalizedPrefixCode_valid hΩ hAC hsub) hm hT hQt hTt
  rw [woodinSparseSuccessorMap_value hΩ hAC hk hm hT hQt hTt hQrank hsp hp]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair,
    normalizedIsomorphismName_empty (hc.system.order.preorder k (mem_succ_self k))
      (hc.system.tops.top k (mem_succ_self k)).1, sparseAppend_empty]

theorem woodinSparseSuccessorMap_section {i p : V} (hi : i ∈ succ k) (hp : p ∈ (forcingCodeP D) ‘ i) :
    (woodinSparseSuccessorMap k c m) ‘ (((forcingCodeE C) ‘ ⟨i, succ k⟩ₖ) ‘ p) =
      (m ‘ k) ‘ (((forcingCodeE D) ‘ ⟨i, k⟩ₖ) ‘ p) := by
  let := hΩ.inaccessible.1
  have hks := hΩ.inaccessible.rankCriterion.2.2.1 k hk
  have hpC : p ∈ (forcingCodeP C) ‘ i := (woodinNormalizedStage_successor_old_carrier hΩ hAC hk hi).symm ▸ hp
  have hz := (woodinNormalizedStageCode_valid hΩ hAC hks).system.split.secMaps
    i (mem_succ_iff.mpr (Or.inr hi)) (succ k) (mem_succ_self (succ k))
    (IsOrdinal.toIsTransitive.transitive _ hi) p hpC
  rw [woodinNormalizedStage_successor_section hΩ hAC hk hi hp] at hz ⊢
  exact woodinSparseSuccessorMap_empty_tail hΩ hAC hk hm hT hQt hTt hQrank hsp hz

theorem woodinSparseSuccessorMap_top
    (ht : (m ‘ k) ‘ ((forcingCodet D) ‘ k) = ∅) :
    (woodinSparseSuccessorMap k c m) ‘ ((forcingCodet C) ‘ (succ k)) = ∅ := by
  let := hΩ.inaccessible.1
  have hks := hΩ.inaccessible.rankCriterion.2.2.1 k hk
  have hz := ((woodinNormalizedStageCode_valid hΩ hAC hks).system.tops.top (succ k) (mem_succ_self (succ k))).1
  rw [woodinNormalizedStage_successor_top hΩ hAC hk] at hz ⊢
  rw [woodinSparseSuccessorMap_empty_tail hΩ hAC hk hm hT hQt hTt hQrank hsp hz, ht]

theorem woodinSparseSuccessorMap_projection {i z : V} (hi : i ∈ succ k)
    (hz : z ∈ (forcingCodeP C) ‘ (succ k))
    (hπ : ∀ i ∈ succ k, ∀ j ∈ succ k, i ⊆ j → ∀ p ∈ Q ‘ j,
      ((forcingRecodedProjections (succ k) (woodinNormalizedPrefixCode (succ k)) m) ‘ ⟨i, j⟩ₖ) ‘ p =
        p ↾ (succ (woodinSourceIndex i))) :
    ((woodinSparseSuccessorMap k c m) ‘ z) ↾ (succ (woodinSourceIndex i)) =
      (m ‘ i) ‘ (((forcingCodeπ C) ‘ ⟨i, succ k⟩ₖ) ‘ z) := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ (hΩ.inaccessible.rankCriterion.2.2.1 k hk)
  have hs := woodinNormalizedPrefixCode_valid hΩ hAC hsub
  have hb : succ (woodinSourceIndex i) ⊆ woodinSourceIndex (succ k) := by
    rw [woodinSourceIndex_successor]
    rcases mem_succ_iff.mp hi with rfl | hik
    · exact subset_refl _
    · simpa only [woodinSparseBounds_value hi, woodinSparseBounds_value (mem_succ_self k)] using
        woodinSparseBounds_mono hik (mem_succ_self k)
  have hpD : kpair.π₁ z ∈ (forcingCodeP D) ‘ k := by
    rw [(woodinNormalizedStage_successor_eq hΩ hAC hk).1] at hz
    obtain ⟨p, hp, τ, _, rfl⟩ := mem_prod_iff.mp hz
    simpa only [kpair.π₁_kpair] using hp
  have hpN : kpair.π₁ z ∈ (forcingCodeP (woodinNormalizedPrefixCode (succ k))) ‘ k := by
    rwa [woodinNormalizedPrefix_successor hΩ hAC hk]
  have hik : i ⊆ k := by
    rcases mem_succ_iff.mp hi with rfl | hi' 
    · exact subset_refl _
    · exact IsOrdinal.toIsTransitive.transitive _ hi'
  have hbase := woodinSparseSuccessorMap_base_mem hΩ hAC hk hm hT hQt hTt hQrank hz
  have he := forcingRecodedProjections_image hs hm hi (mem_succ_self k)
    hik hpN
  rw [hπ i hi k (mem_succ_self k) hik _ hbase] at he
  rw [woodinNormalizedPrefix_successor hΩ hAC hk] at he
  rw [← restrict_restrict_of_subset hb,
    woodinSparseSuccessorMap_restrict hΩ hAC hk hm hT hQt hTt hQrank hsp hz,
    woodinNormalizedStage_successor_projection hΩ hAC hk hi hz]
  exact he

end ZFVP
