import ZFVP.SetTheory.ChoicelessInaccessibleRank
import ZFVP.SetTheory.RankCollection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem leastWitnessStageOrZero_mem_inaccessible {δ : V}
    (hδ : IsChoicelessInaccessible δ) (R : V → V → Prop) (hR : ℒₛₑₜ-relation R)
    {x : V} (hex : (∃ y, R x y) → ∃ y ∈ hierarchy δ, R x y) :
    leastWitnessStageOrZero R hR x ∈ δ := by
  classical
  let := hδ.1
  by_cases hx : ∃ y, R x y
  · obtain ⟨y, hy, hxy⟩ := hex hx
    have hs := leastWitnessStageOrZero_spec R hR x hx
    have hr := (mem_hierarchy_iff_rank_mem y δ).mp hy
    have hm : leastWitnessStageOrZero R hR x ⊆ succ (rank y) := hs.2.2 _ inferInstance
      ⟨y, by rw [hierarchy_succ, mem_power_iff]; exact subset_hierarchy_rank y, hxy⟩
    exact ordinal_mem_of_subset_mem hm (regularCardinal_succ_closed hδ.regular hr)
  · have he : (0 : V) = leastWitnessStageOrZero R hR x :=
      (leastWitnessStageOrZero_eq_iff R hR x 0).mpr (Or.inr ⟨hx, rfl⟩)
    rw [← he]
    exact hδ.regular.2.1 0 (by simp)

theorem witnessBoundingStep_mem_inaccessible {δ α : V} (hδ : IsChoicelessInaccessible δ)
    (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (hα : α ∈ δ)
    (hex : ∀ x ∈ hierarchy α, (∃ y, R x y) → ∃ y ∈ hierarchy δ, R x y) :
    witnessBoundingStep R hR α ∈ δ := by
  let := hδ.1
  let := IsOrdinal.of_mem hα
  have hn : NoLowRankCofinalMaps δ := fun _ hx _ ↦ hδ.no_rank_cofinalMap hx
  obtain ⟨β, hβ, hb⟩ := hn.definable_map_bounded (hierarchy_mem hα)
    (leastWitnessStageOrZero R hR) (by definability)
    (fun x hx ↦ leastWitnessStageOrZero_mem_inaccessible hδ R hR (hex x hx))
  let := IsOrdinal.of_mem hβ
  have huord : IsOrdinal (⋃ˢ repl (leastWitnessStageOrZero R hR) (by definability) (hierarchy α)) :=
    IsOrdinal.sUnion (by
      intro z hz
      obtain ⟨x, _, rfl⟩ := (repl_spec (leastWitnessStageOrZero_definable R hR)).mp hz
      infer_instance)
  have hu : ⋃ˢ repl (leastWitnessStageOrZero R hR) (by definability) (hierarchy α) ⊆ β := by
    intro z hz
    obtain ⟨y, hy, hzy⟩ := mem_sUnion_iff.mp hz
    obtain ⟨x, hx, rfl⟩ := (repl_spec (leastWitnessStageOrZero_definable R hR)).mp hy
    exact IsOrdinal.toIsTransitive.mem_trans hzy (hb x hx)
  exact regularCardinal_succ_closed hδ.regular
    (ordinal_union_mem hα (ordinal_mem_of_subset_mem hu hβ))

end ZFVP
