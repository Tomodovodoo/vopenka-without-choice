import ZFVP.ModelTheory.ClassForcingTowerGeneric
import ZFVP.ModelTheory.ClassForcingTowerSplitProjection
import ZFVP.ModelTheory.ProjectionNameTransport
import ZFVP.ModelTheory.TwoStepInclusion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace DefinableForcingTower
variable (T : DefinableForcingTower V) {G : Set V}

theorem stageFilter_projection (hG : IsExternalClassForcingFilter T.Condition T.LE G)
    {i j : V} [IsOrdinal i] [IsOrdinal j] (hij : i ⊆ j) :
    forcingProjectionGeneric (T.P i) (T.R i) (T.projection i j) (T.stageFilter G j) =
      T.stageFilter G i := by
  apply Set.ext
  intro p
  constructor
  · intro hp
    have hpP := hp.1
    have hsec := ((T.splitProjection hij).generic_iff_section (T.order i inferInstance)
      (T.stageFilter_isFilter hG j) hpP).mp hp
    exact ⟨hpP, hG.2.2.1 _ hsec.2 _
      ((T.condition_pair i p).mpr ⟨inferInstance, hpP⟩) (T.section_equivalent hij hpP).2⟩
  · intro hp
    apply ((T.splitProjection hij).generic_iff_section (T.order i inferInstance)
      (T.stageFilter_isFilter hG j) hp.1).mpr
    have he := T.section_mem hij hp.1
    exact ⟨he, hG.2.2.1 _ hp.2 _
      ((T.condition_pair j _).mpr ⟨inferInstance, he⟩) (T.section_equivalent hij hp.1).1⟩

noncomputable def stageInclusion
    (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)
    {i j : V} [IsOrdinal i] [IsOrdinal j] (hij : i ⊆ j) :
    MembershipEndExtension (T.stageContext hG i).Model (T.stageContext hG j).Model :=
  (T.stageContext hG i).projectionInclusion (T.stageContext hG j)
    (T.splitProjection hij) (T.stageFilter_projection hG.1 hij)

theorem stageInclusion_check
    (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)
    {i j : V} [IsOrdinal i] [IsOrdinal j] (hij : i ⊆ j) (x : V) :
    T.stageInclusion hG hij ((T.stageContext hG i).check x) = (T.stageContext hG j).check x :=
  (T.stageContext hG i).projectionInclusion_check (T.stageContext hG j)
    (T.splitProjection hij) (T.stageFilter_projection hG.1 hij) x

theorem stageInclusion_name
    (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)
    {i j : V} [IsOrdinal i] [IsOrdinal j] (hij : i ⊆ j) (σ : ForcingName (T.P i)) :
    (T.stageContext hG j).ofName
      ⟨nameAction (T.sectionMap i j) σ.val,
        nameAction_isName (T.section_function i j inferInstance inferInstance hij) σ.property⟩ =
      T.stageInclusion hG hij ((T.stageContext hG i).ofName σ) :=
  (T.stageContext hG i).projectionInclusion_nameAction (T.stageContext hG j)
    (T.splitProjection hij) (T.stageFilter_projection hG.1 hij) σ

theorem stageInclusion_comp
    (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)
    {i j k : V} [IsOrdinal i] [IsOrdinal j] [IsOrdinal k] (hij : i ⊆ j) (hjk : j ⊆ k)
    (x : (T.stageContext hG i).Model) :
    T.stageInclusion hG hjk (T.stageInclusion hG hij x) =
      T.stageInclusion hG (subset_trans hij hjk) x := by
  apply (T.stageContext hG i).endExtension_ext
    ((T.stageInclusion hG hjk).comp (T.stageInclusion hG hij))
    (T.stageInclusion hG (subset_trans hij hjk))
  intro a
  change T.stageInclusion hG hjk (T.stageInclusion hG hij ((T.stageContext hG i).check a)) =
    T.stageInclusion hG (subset_trans hij hjk) ((T.stageContext hG i).check a)
  rw [T.stageInclusion_check, T.stageInclusion_check, T.stageInclusion_check]

end DefinableForcingTower
end ZFVP
