import ZFVP.SetTheory.RankEnumerations
import ZFVP.SetTheory.ChoicelessInaccessibleRank
import ZFVP.SetTheory.WellOrderedSurjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem HasShortRankEnumerations.inaccessible {κ : V}
    (h : HasShortRankEnumerations κ κ) (hr : IsRegularCardinal κ) (hω : (ω : V) ∈ κ) :
    IsChoicelessInaccessible κ := by
  let := hr.1.1
  refine ⟨inferInstance, hω, ?_⟩
  intro α hα g hg
  obtain ⟨γ, hγ, e, he, her⟩ := h α hα
  exact no_cofinalMap_below_cofinality (hr.2.2.symm ▸ hγ)
    ⟨compose e g, cofinalMap_precompose_surjection hg he her⟩

theorem HasShortRankEnumerations.hierarchy_wellOrderable {θ κ α : V} [IsOrdinal κ]
    (h : HasShortRankEnumerations θ κ) (hα : α ∈ θ) : IsWellOrderable (hierarchy α) := by
  obtain ⟨γ, hγ, e, he, her⟩ := h α hα
  let := IsOrdinal.of_mem hγ
  exact wellOrderable_of_cardLE (cardLE_of_surjective_function (ordinal_wellOrderable γ) he her)
    (ordinal_wellOrderable γ)

theorem HasShortRankEnumerations.member_wellOrderable {θ κ X : V} [IsOrdinal θ] [IsOrdinal κ]
    (h : HasShortRankEnumerations θ κ) (hX : X ∈ hierarchy θ) : IsWellOrderable X :=
  wellOrderable_of_cardLE (cardLE_of_subset (subset_hierarchy_rank X))
    (h.hierarchy_wellOrderable ((mem_hierarchy_iff_rank_mem X θ).mp hX))

end ZFVP
