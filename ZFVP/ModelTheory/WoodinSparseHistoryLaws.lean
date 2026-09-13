import ZFVP.ModelTheory.WoodinSparseRow
import ZFVP.ModelTheory.WoodinNormalizedPrefixColumns

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal θ]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
variable (ih : ∀ i ∈ θ, IsWoodinSparseRow i (woodinSparseRecodingRec i))

local notation "Q" => woodinRecodingCarriers (woodinSparseRecodingHistory θ)
local notation "T" => woodinRecodingOrders (woodinSparseRecodingHistory θ)
local notation "m" => woodinRecodingMaps (woodinSparseRecodingHistory θ)
local notation "N" => woodinNormalizedPrefixCode θ

include ih in
theorem woodinSparseHistory_sparse {i p : V} (hi : i ∈ θ) (hp : p ∈ Q ‘ i) :
    IsSparseFunctionOn (succ (woodinSourceIndex i)) p := by
  rw [(woodinSparseRecodingHistory_values hi).1] at hp
  exact (ih i hi).2.1 p hp

include hΩ hAC hθ ih in
theorem woodinSparseHistory_family :
    ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP N) ‘ i) ((forcingCodeR N) ‘ i)
      (Q ‘ i) (T ‘ i) (m ‘ i) :=
  woodinSparseRecodingHistory_family_of_rows hΩ hAC hθ (fun i hi ↦ (ih i hi).1.1)

include ih in
theorem woodinSparseHistory_preorder {i : V} (hi : i ∈ θ) :
    IsForcingPreorder (Q ‘ i) (T ‘ i) := by
  rw [(woodinSparseRecodingHistory_values hi).1, (woodinSparseRecodingHistory_values hi).2.1]
  exact (ih i hi).1.2.1

include ih in
theorem woodinSparseHistory_small {i ξ : V} (hi : i ∈ θ) (hξ : IsChoicelessInaccessible ξ)
    (hcard : (kpair.π₂ (woodinIterationRec i)) ‘ i ∈ ξ) : Q ‘ i ∈ hierarchy ξ := by
  rw [(woodinSparseRecodingHistory_values hi).1]
  exact (ih i hi).1.2.2 ξ hξ hcard

include hΩ hAC hθ ih in
theorem woodinSparseHistory_top {i : V} (hi : i ∈ θ) :
    (forcingRecodedTops θ N m) ‘ i = ∅ := by
  rw [forcingRecodedTops_value hi, woodinNormalizedPrefix_stage_top hΩ hAC hθ hi,
    (woodinSparseRecodingHistory_values hi).2.2]
  exact (ih i hi).2.2.1

include hΩ hAC hθ ih in
theorem woodinSparseHistory_projection {i j p : V} (hi : i ∈ θ) (hj : j ∈ θ)
    (hij : i ⊆ j) (hp : p ∈ Q ‘ j) :
    ((forcingRecodedProjections θ N m) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)) := by
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  have hs := woodinNormalizedPrefixCode_valid hΩ hAC hθ
  have hm := woodinSparseHistory_family hΩ hAC hθ ih
  obtain ⟨z, hz, rfl⟩ := (hm j hj).surjective p hp
  rw [forcingRecodedProjections_image hs hm hi hj hij hz]
  rcases IsOrdinal.subset_iff.mp hij with rfl | hij
  · rw [hs.system.split.projId hi hz]
    have hsp := woodinSparseHistory_sparse ih hi (function_value_mem (hm i hi).1 hz)
    let := hsp.1
    exact (IsFunction.restrict_eq_self _ _ hsp.2.1).symm
  · rw [woodinNormalizedPrefix_stage_projection hΩ hAC hθ hj (mem_succ_iff.mpr (Or.inr hij)),
      (woodinSparseRecodingHistory_values hi).2.2, (woodinSparseRecodingHistory_values hj).2.2]
    rw [woodinNormalizedPrefix_stage_carrier hΩ hAC hθ hj (mem_succ_self j)] at hz
    exact ((ih j hj).2.2.2.1 i hij z hz).symm

include hΩ hAC hθ ih in
theorem woodinSparseHistory_section {i j p : V} (hi : i ∈ θ) (hj : j ∈ θ)
    (hij : i ⊆ j) (hp : p ∈ Q ‘ i) :
    ((forcingRecodedSections θ N m) ‘ ⟨i, j⟩ₖ) ‘ p = p := by
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  have hs := woodinNormalizedPrefixCode_valid hΩ hAC hθ
  have hm := woodinSparseHistory_family hΩ hAC hθ ih
  obtain ⟨z, hz, rfl⟩ := (hm i hi).surjective p hp
  rw [forcingRecodedSections_image hs hm hi hj hij hz]
  rcases IsOrdinal.subset_iff.mp hij with rfl | hij
  · rw [hs.system.split.secId i hi z hz]
  · rw [woodinNormalizedPrefix_stage_section hΩ hAC hθ hj (mem_succ_iff.mpr (Or.inr hij)),
      (woodinSparseRecodingHistory_values hi).2.2, (woodinSparseRecodingHistory_values hj).2.2]
    rw [woodinNormalizedPrefix_stage_carrier hΩ hAC hθ hj (mem_succ_iff.mpr (Or.inr hij))] at hz
    exact (ih j hj).2.2.2.2 i hij z hz

end ZFVP
