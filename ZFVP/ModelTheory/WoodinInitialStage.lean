import ZFVP.ModelTheory.ForcingOmegaTruth
import ZFVP.ModelTheory.WoodinSuccessorBounds
import ZFVP.SetTheory.ForcingIterationInitial
import ZFVP.SetTheory.WoodinSeedCardinal
import ZFVP.ModelTheory.SingletonForcingTruth

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSeedStage : V :=
  woodinStageCode {∅} (({∅} : V) ×ˢ {∅}) ∅ woodinSeedCardinal

noncomputable def woodinInitialStage : V := woodinSuccessorStep (woodinSeedStage : V)

theorem woodinSeedStage_stage : IsWoodinStage (woodinSeedStage : V) := by
  simp only [woodinSeedStage, IsWoodinStage, woodinStagePoset_code, woodinStageOrder_code,
    woodinStageTop_code, woodinStageCardinal_code]
  refine ⟨singletonForcing_preorder ∅, singletonForcing_top ∅, inferInstance, ?_, ?_⟩
  · intro p hp
    have he : p = ∅ := mem_singleton_iff.mp hp
    subst p
    exact (singletonForcing_checked_truth ∅ woodinSeedCardinal regularCardinalFormula).mpr
      ((Defined.eval_iff _).mpr woodinSeedCardinal_regular)
  · intro p hp
    have he : p = ∅ := mem_singleton_iff.mp hp
    subst p
    exact (singletonForcing_checked_truth ∅ woodinSeedCardinal dependentChoiceBelowFormula).mpr
      ((Defined.eval_iff _).mpr woodinSeedCardinal_DC)

theorem woodinSeedStage_small : IsWoodinStageSmall (woodinSeedStage : V) := by
  intro θ hθ _
  let := hθ.1
  have h0 : (∅ : V) ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr (hθ.regular.2.1 ∅ (by simp))
  simpa [woodinSeedStage] using pair_mem_hierarchy_limit hθ.rankCriterion.2.2.1 h0 h0

theorem woodinInitialStage_properties {δ : V} (hδ : IsWoodinSupercompact δ) :
    IsWoodinStage (woodinInitialStage : V) ∧ IsWoodinStageSmall (woodinInitialStage : V) ∧
      IsChoicelessInaccessible (woodinStageCardinal (woodinInitialStage : V)) ∧
      (ω : V) ∈ woodinStageCardinal (woodinInitialStage : V) ∧
      woodinStageCardinal (woodinInitialStage : V) ∈ δ := by
  have hω : woodinStageCardinal (woodinSeedStage : V) ∈ δ := by
    simpa [woodinSeedStage] using woodinSeedCardinal_lt hδ
  have hn := woodinSuccessorStep_preserves_below_supercompact
    woodinSeedStage_stage woodinSeedStage_small hδ hω
  refine ⟨hn.1, hn.2.1, hn.2.2.1, ?_, hn.2.2.2.2⟩
  let : IsOrdinal (woodinStageCardinal (woodinInitialStage : V)) := hn.2.2.1.1
  apply ordinal_mem_of_subset_mem woodinSeedCardinal_omega_subset
  simpa only [woodinInitialStage, woodinSeedStage, woodinStageCardinal_code] using hn.2.2.2.1

end ZFVP
