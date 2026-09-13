import ZFVP.ModelTheory.ClassForcingTowerStageModels
import ZFVP.ModelTheory.ClassForcingTowerBoundedModels
import ZFVP.ModelTheory.ForcingContextCongruence
import ZFVP.ModelTheory.ForcingBaseChange
import ZFVP.ModelTheory.TwoStepInclusion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace DefinableForcingTower
variable (T : DefinableForcingTower V) {G : Set V}
  (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)

theorem stageDenseImage_eq_bounded (i : V) [IsOrdinal i] :
    (T.stageContext hG i).denseImage (T.bounded_preorder i) (T.bounded_top i) (T.stageEmbedding_dense i) =
      T.boundedContext hG i := by
  apply ForcingContext.eq_of_data_eq
  · rfl
  · rfl
  · rfl
  · exact (T.boundedFilter_eq_denseImage hG.1 i).symm

noncomputable def stageBoundedEquiv (i : V) [IsOrdinal i] :
    (T.stageContext hG i).Model ≃ (T.boundedContext hG i).Model :=
  ((T.stageContext hG i).denseEquiv (T.bounded_preorder i) (T.bounded_top i) (T.stageEmbedding_dense i)).trans
    (ForcingContext.modelCongr (T.stageDenseImage_eq_bounded hG i))

theorem stageBoundedEquiv_mem_iff (i : V) [IsOrdinal i] (x y : (T.stageContext hG i).Model) :
    T.stageBoundedEquiv hG i x ∈ T.stageBoundedEquiv hG i y ↔ x ∈ y :=
  (ForcingContext.modelCongr_mem_iff (T.stageDenseImage_eq_bounded hG i) _ _).trans
    ((T.stageContext hG i).denseEquiv_mem_iff (T.bounded_preorder i) (T.bounded_top i)
      (T.stageEmbedding_dense i) x y)

theorem stageBoundedEquiv_check (i : V) [IsOrdinal i] (x : V) :
    T.stageBoundedEquiv hG i ((T.stageContext hG i).check x) = (T.boundedContext hG i).check x := by
  exact (congrArg (ForcingContext.modelCongr (T.stageDenseImage_eq_bounded hG i))
    ((T.stageContext hG i).denseEquiv_check (T.bounded_preorder i) (T.bounded_top i)
      (T.stageEmbedding_dense i) x)).trans
    (ForcingContext.modelCongr_check (T.stageDenseImage_eq_bounded hG i) x)

noncomputable def stageToBounded (i : V) [IsOrdinal i] :
    MembershipEndExtension (T.stageContext hG i).Model (T.boundedContext hG i).Model :=
  MembershipEndExtension.ofEquiv (T.stageBoundedEquiv hG i) (T.stageBoundedEquiv_mem_iff hG i)

theorem stageToBounded_check (i : V) [IsOrdinal i] (x : V) :
    T.stageToBounded hG i ((T.stageContext hG i).check x) = (T.boundedContext hG i).check x :=
  T.stageBoundedEquiv_check hG i x

theorem stageBoundedEquiv_commutes {i j : V} [IsOrdinal i] [IsOrdinal j] (hij : i ⊆ j)
    (x : (T.stageContext hG i).Model) :
    T.boundedInclusion hG hij (T.stageBoundedEquiv hG i x) =
      T.stageBoundedEquiv hG j (T.stageInclusion hG hij x) := by
  apply (T.stageContext hG i).endExtension_ext
    ((T.boundedInclusion hG hij).comp (T.stageToBounded hG i))
    ((T.stageToBounded hG j).comp (T.stageInclusion hG hij))
  intro a
  change T.boundedInclusion hG hij (T.stageBoundedEquiv hG i ((T.stageContext hG i).check a)) =
    T.stageBoundedEquiv hG j (T.stageInclusion hG hij ((T.stageContext hG i).check a))
  rw [T.stageBoundedEquiv_check, T.boundedInclusion_check, T.stageInclusion_check,
    T.stageBoundedEquiv_check]

end DefinableForcingTower
end ZFVP
