import ZFVP.SetTheory.ClassForcingTowerStages
import ZFVP.SetTheory.ClassForcingTowerProjection
import ZFVP.ModelTheory.ClassForcingTowerSplitProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

noncomputable def boundedReduction (j : V) : V :=
  definableGraph (T.boundedConditions j) (T.reduceCondition j) (by definability)

noncomputable def boundedProjection (i j : V) : V :=
  definableGraph (T.boundedConditions j) (T.projectCondition i) (by definability)

theorem boundedReduction_value {j c : V} (hc : c ∈ T.boundedConditions j) :
    (T.boundedReduction j) ‘ c = T.reduceCondition j c := value_definableGraph _ _ _ hc

theorem boundedProjection_value {i j c : V} (hc : c ∈ T.boundedConditions j) :
    (T.boundedProjection i j) ‘ c = T.projectCondition i c := value_definableGraph _ _ _ hc

theorem boundedReduction_maps (j : V) [IsOrdinal j] :
    T.boundedReduction j ∈ (T.P j) ^ (T.boundedConditions j) :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ hc ↦ T.reduceCondition_mem hc)

theorem boundedProjection_maps (i j : V) [IsOrdinal i] [IsOrdinal j] :
    T.boundedProjection i j ∈ (T.P i) ^ (T.boundedConditions j) :=
  definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun _ hc ↦ T.projectCondition_mem (T.boundedConditions_condition hc))

theorem reduceCondition_tagged {j p : V} [IsOrdinal j] (hp : p ∈ T.P j) :
    T.reduceCondition j ⟨j, p⟩ₖ = p := by
  simp only [reduceCondition, kpair.π₁_kpair, kpair.π₂_kpair, T.section_self j inferInstance p hp]

theorem boundedReduction_tagged {j p : V} [IsOrdinal j] (hp : p ∈ T.P j) :
    (T.boundedReduction j) ‘ ⟨j, p⟩ₖ = p := by
  rw [T.boundedReduction_value (T.tagged_mem_boundedConditions (subset_refl j) hp),
    T.reduceCondition_tagged hp]

theorem reduceCondition_order_iff {j c d : V} [IsOrdinal j]
    (hc : c ∈ T.boundedConditions j) (hd : d ∈ T.boundedConditions j) :
    ⟨T.reduceCondition j c, T.reduceCondition j d⟩ₖ ∈ T.R j ↔
      ⟨c, d⟩ₖ ∈ T.boundedOrder j := by
  have hec := T.reduceCondition_equivalent hc
  have hed := T.reduceCondition_equivalent hd
  rw [← T.le_sameStage_iff (T.reduceCondition_mem hc) (T.reduceCondition_mem hd),
    T.pair_mem_boundedOrder]
  constructor
  · intro h
    exact ⟨hc, hd, T.le_trans hec.2 (T.le_trans h hed.1)⟩
  · intro h
    exact T.le_trans hec.1 (T.le_trans h.2.2 hed.2)

theorem boundedReduction_order_iff {j c d : V} [IsOrdinal j]
    (hc : c ∈ T.boundedConditions j) (hd : d ∈ T.boundedConditions j) :
    ⟨(T.boundedReduction j) ‘ c, (T.boundedReduction j) ‘ d⟩ₖ ∈ T.R j ↔
      ⟨c, d⟩ₖ ∈ T.boundedOrder j := by
  rw [T.boundedReduction_value hc, T.boundedReduction_value hd]
  exact T.reduceCondition_order_iff hc hd

theorem boundedReduction_splitProjection (j : V) [IsOrdinal j] :
    IsForcingSplitProjection (T.P j) (T.R j) (T.boundedConditions j) (T.boundedOrder j)
      (T.boundedReduction j) (T.stageEmbedding j) := by
  have htag (p : V) (hp : p ∈ T.P j) := T.tagged_mem_boundedConditions (subset_refl j) hp
  refine ⟨⟨T.boundedReduction_maps j, ?_, ?_⟩, (T.stageEmbedding_dense j).1, ?_, ?_⟩
  · intro c hc d hd hcd
    exact (T.boundedReduction_order_iff hc hd).mpr hcd
  · intro c hc p hp hpc
    refine ⟨⟨j, p⟩ₖ, htag p hp, ?_, T.boundedReduction_tagged hp⟩
    apply (T.boundedReduction_order_iff (htag p hp) hc).mp
    rwa [T.boundedReduction_tagged hp]
  · intro p hp
    rw [T.stageEmbedding_value hp, T.boundedReduction_tagged hp]
  · intro c hc p hp
    rw [T.stageEmbedding_value hp, ← T.boundedReduction_order_iff hc (htag p hp),
      T.boundedReduction_tagged hp]

theorem reduceCondition_stage {j K c : V} [IsOrdinal j] [IsOrdinal K]
    (hjK : j ⊆ K) (hc : c ∈ T.boundedConditions j) :
    T.reduceCondition K c = (T.sectionMap j K) ‘ (T.reduceCondition j c) := by
  have hs := T.condition_spec (T.boundedConditions_condition hc)
  let := hs.1
  exact (T.section_comp _ j K inferInstance inferInstance inferInstance
    (T.boundedConditions_stage hc) hjK _ hs.2.1).symm

theorem boundedProjection_reduce {i j c : V} [IsOrdinal i] [IsOrdinal j]
    (hij : i ⊆ j) (hc : c ∈ T.boundedConditions j) :
    (T.projection i j) ‘ (T.reduceCondition j c) = T.projectCondition i c := by
  have hs := T.condition_spec (T.boundedConditions_condition hc)
  let := hs.1
  have hu : IsOrdinal (i ∪ kpair.π₁ c) := ordinal_union_ordinal _ _
  have huj : i ∪ kpair.π₁ c ⊆ j := by
    intro x hx
    rcases mem_union_iff.mp hx with hx | hx
    · exact hij x hx
    · exact T.boundedConditions_stage hc x hx
  have hsu := T.section_mem (subset_union_right i (kpair.π₁ c)) hs.2.1
  unfold reduceCondition projectCondition
  rw [← T.section_comp _ (i ∪ kpair.π₁ c) j inferInstance inferInstance inferInstance
    (subset_union_right _ _) huj _ hs.2.1,
    ← T.projection_comp i (i ∪ kpair.π₁ c) j inferInstance inferInstance inferInstance
      (subset_union_left _ _) huj _ (T.section_mem huj hsu),
    T.projection_section _ j inferInstance inferInstance huj _ hsu]

theorem boundedProjection_factor {i j c : V} [IsOrdinal i] [IsOrdinal j]
    (hij : i ⊆ j) (hc : c ∈ T.boundedConditions j) :
    (T.boundedProjection i j) ‘ c = (T.projection i j) ‘ ((T.boundedReduction j) ‘ c) := by
  rw [T.boundedProjection_value hc, T.boundedReduction_value hc, T.boundedProjection_reduce hij hc]

theorem boundedProjection_tagged {i j p : V} [IsOrdinal i] [IsOrdinal j]
    (hij : i ⊆ j) (hp : p ∈ T.P j) :
    (T.boundedProjection i j) ‘ ⟨j, p⟩ₖ = (T.projection i j) ‘ p := by
  rw [T.boundedProjection_factor hij (T.tagged_mem_boundedConditions (subset_refl j) hp),
    T.boundedReduction_tagged hp]

end DefinableForcingTower
end ZFVP
