import ZFVP.ModelTheory.ClassForcingTowerGeneric
import ZFVP.SetTheory.ClassForcingTowerNames
import ZFVP.ModelTheory.DenseEmbeddingTransfer
import ZFVP.ModelTheory.ForcingGenericInclusion

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace DefinableForcingTower

variable (T : DefinableForcingTower V) {G : Set V}

theorem boundedConditions_mono {i j : V} [IsOrdinal i] [IsOrdinal j] (hij : i ⊆ j) :
    T.boundedConditions i ⊆ T.boundedConditions j := by
  intro c hc
  have hs := T.condition_spec (T.boundedConditions_condition hc)
  have := hs.1
  rw [hs.2.2]
  exact T.tagged_mem_boundedConditions
    (fun x hx ↦ hij x (T.boundedConditions_stage hc x hx)) hs.2.1

def boundedFilter (G : Set V) (i : V) : Set V :=
  {c | c ∈ T.boundedConditions i ∧ c ∈ G}

theorem boundedFilter_eq_denseImage
    (hG : IsExternalClassForcingFilter T.Condition T.LE G) (i : V) [IsOrdinal i] :
    T.boundedFilter G i = denseImageFilter (T.boundedConditions i) (T.boundedOrder i)
      (T.stageEmbedding i) (T.stageFilter G i) := by
  ext c
  constructor
  · rintro ⟨hc, hcG⟩
    have hr := T.reduceCondition_mem hc
    have he := T.reduceCondition_equivalent hc
    refine ⟨hc, T.reduceCondition i c, ⟨hr, ?_⟩, ?_⟩
    · exact hG.2.2.1 c hcG _
        ((T.condition_pair _ _).mpr ⟨inferInstance, hr⟩) he.2
    · rw [T.stageEmbedding_value hr]
      exact (T.pair_mem_boundedOrder _ _ _).mpr
        ⟨T.tagged_mem_boundedConditions (subset_refl _) hr, hc, he.1⟩
  · rintro ⟨hc, p, hp, hpc⟩
    rw [T.stageEmbedding_value hp.1] at hpc
    exact ⟨hc, hG.2.2.1 _ hp.2 c (T.boundedConditions_condition hc)
      ((T.pair_mem_boundedOrder _ _ _).mp hpc).2.2⟩

theorem boundedFilter_generic
    (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)
    (i : V) [IsOrdinal i] :
    IsExternalForcingGeneric (T.boundedConditions i) (T.boundedOrder i) (T.boundedFilter G i) := by
  rw [T.boundedFilter_eq_denseImage hG.1 i]
  exact denseImageFilter_generic (T.order i inferInstance) (T.bounded_preorder i)
    (T.stageEmbedding_dense i) (T.stageFilter_generic hG i)

noncomputable def boundedContext
    (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)
    (i : V) [IsOrdinal i] : ForcingContext V :=
  ⟨T.boundedConditions i, T.boundedOrder i, T.one, T.boundedFilter G i,
    T.bounded_preorder i, T.bounded_top i, T.boundedFilter_generic hG i⟩

theorem boundedContext_models_zf
    (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)
    (i : V) [IsOrdinal i] : (T.boundedContext hG i).Model↓[ℒₛₑₜ] ⊧* 𝗭𝗙 :=
  inferInstance

variable (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)

theorem boundedFilter_restrict {i j : V} [IsOrdinal i] [IsOrdinal j] (hij : i ⊆ j)
    (p : V) : p ∈ T.boundedFilter G i ↔
      p ∈ T.boundedFilter G j ∧ p ∈ T.boundedConditions i := by
  constructor
  · rintro ⟨hp, hpG⟩
    exact ⟨⟨T.boundedConditions_mono hij p hp, hpG⟩, hp⟩
  · rintro ⟨⟨_, hpG⟩, hp⟩
    exact ⟨hp, hpG⟩

noncomputable def boundedInclusion {i j : V} [IsOrdinal i] [IsOrdinal j] (hij : i ⊆ j) :
    MembershipEndExtension (T.boundedContext hG i).Model (T.boundedContext hG j).Model :=
  (T.boundedContext hG i).genericInclusion (T.boundedContext hG j)
    (T.boundedFilter_restrict hij)

theorem boundedInclusion_ofName {i j : V} [IsOrdinal i] [IsOrdinal j] (hij : i ⊆ j)
    (τ : ForcingName (T.boundedConditions i)) :
    T.boundedInclusion hG hij ((T.boundedContext hG i).ofName τ) =
      (T.boundedContext hG j).ofName ⟨τ.val, τ.property.mono (T.boundedConditions_mono hij)⟩ :=
  (T.boundedContext hG i).genericInclusion_ofName (T.boundedContext hG j)
    (T.boundedConditions_mono hij) (T.boundedFilter_restrict hij) τ

theorem boundedInclusion_check {i j : V} [IsOrdinal i] [IsOrdinal j] (hij : i ⊆ j)
    (x : V) :
    T.boundedInclusion hG hij ((T.boundedContext hG i).check x) =
      (T.boundedContext hG j).check x :=
  (T.boundedContext hG i).genericInclusion_check (T.boundedContext hG j)
    (T.boundedFilter_restrict hij) x

theorem boundedInclusion_self {i : V} [IsOrdinal i]
    (x : (T.boundedContext hG i).Model) : T.boundedInclusion hG (subset_refl i) x = x := by
  obtain ⟨τ, rfl⟩ := (T.boundedContext hG i).ofName_surjective x
  exact T.boundedInclusion_ofName hG (subset_refl i) τ

theorem boundedInclusion_comp {i j k : V} [IsOrdinal i] [IsOrdinal j] [IsOrdinal k]
    (hij : i ⊆ j) (hjk : j ⊆ k) (x : (T.boundedContext hG i).Model) :
    T.boundedInclusion hG hjk (T.boundedInclusion hG hij x) =
      T.boundedInclusion hG (fun z hz ↦ hjk z (hij z hz)) x := by
  obtain ⟨τ, rfl⟩ := (T.boundedContext hG i).ofName_surjective x
  change ForcingName (T.boundedConditions i) at τ
  exact (congrArg (T.boundedInclusion hG hjk) (T.boundedInclusion_ofName hG hij τ)).trans
    ((T.boundedInclusion_ofName hG hjk
      ⟨τ.val, τ.property.mono (T.boundedConditions_mono hij)⟩).trans
      (T.boundedInclusion_ofName hG (fun z hz ↦ hjk z (hij z hz)) τ).symm)

end DefinableForcingTower
end ZFVP
