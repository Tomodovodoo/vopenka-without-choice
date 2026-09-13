import ZFVP.SetTheory.ClassForcingTowerProjection
import ZFVP.ModelTheory.DefinableClassGeneric
import ZFVP.ModelTheory.ForcingModel

/-! A generic for the definable proper-class direct limit induces an
ordinary generic at every set stage. The proof uses the complete
projections constructed from the tower; stage genericity is not assumed. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace DefinableForcingTower

variable (T : DefinableForcingTower V) {G : Set V}

def stageFilter (G : Set V) (i : V) : Set V :=
  {p | p ∈ T.P i ∧ ⟨i, p⟩ₖ ∈ G}

theorem stageFilter_isFilter (hG : IsExternalClassForcingFilter T.Condition T.LE G)
    (i : V) [IsOrdinal i] :
    IsExternalForcingFilter (T.P i) (T.R i) (T.stageFilter G i) := by
  have hproject {c : V} (hc : c ∈ G) : T.projectCondition i c ∈ T.stageFilter G i := by
    have hcp := hG.1 c hc
    have hp := T.projectCondition_mem (i := i) hcp
    exact ⟨hp, hG.2.2.1 c hc _ ((T.condition_pair _ _).mpr ⟨inferInstance, hp⟩)
      (T.below_projectCondition hcp)⟩
  refine ⟨fun p hp ↦ hp.1, ?_, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := hG.2.1
    exact ⟨T.projectCondition i c, hproject hc⟩
  · intro p hp q hq hpq
    exact ⟨hq, hG.2.2.1 _ hp.2 _
      ((T.condition_pair _ _).mpr ⟨inferInstance, hq⟩)
      ((T.le_sameStage_iff hp.1 hq).mpr hpq)⟩
  · intro p hp q hq
    obtain ⟨c, hc, hcp, hcq⟩ := hG.2.2.2 _ hp.2 _ hq.2
    exact ⟨T.projectCondition i c, hproject hc,
      (T.below_stage_iff (hG.1 c hc) hp.1).mp hcp,
      (T.below_stage_iff (hG.1 c hc) hq.1).mp hcq⟩

theorem stageFilter_generic
    (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)
    (i : V) [IsOrdinal i] :
    IsExternalForcingGeneric (T.P i) (T.R i) (T.stageFilter G i) := by
  refine ⟨T.stageFilter_isFilter hG.1 i, ?_⟩
  intro D hD
  obtain ⟨c, hcG, hc, p, hpD, hcp⟩ :=
    hG.2 (T.stageDenseClass i D) (T.stageDenseClass_definable i D)
      (T.stageDenseClass_dense hD)
  have hp := hD.1 p hpD
  exact ⟨p, ⟨hp, hG.1.2.2.1 c hcG _
    ((T.condition_pair _ _).mpr ⟨inferInstance, hp⟩) hcp⟩, hpD⟩

noncomputable def stageContext
    (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)
    (i : V) [IsOrdinal i] : ForcingContext V :=
  ⟨T.P i, T.R i, T.top i, T.stageFilter G i, T.order i inferInstance,
    T.top_spec i inferInstance, T.stageFilter_generic hG i⟩

theorem stageContext_models_zf
    (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)
    (i : V) [IsOrdinal i] : (T.stageContext hG i).Model↓[ℒₛₑₜ] ⊧* 𝗭𝗙 :=
  inferInstance

end DefinableForcingTower
end ZFVP
