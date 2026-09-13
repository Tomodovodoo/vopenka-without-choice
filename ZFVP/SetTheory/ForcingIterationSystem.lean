import ZFVP.SetTheory.ForcingOrderExtension
import ZFVP.SetTheory.ForcingTopExtension
import ZFVP.SetTheory.ForcingMapExtension
import ZFVP.SetTheory.ForcingLiftSectionCompatibility

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The algebraic invariant maintained by the stage constructors. -/
structure IsForcingIterationSystem (θ P R π E L t : V) : Prop where
  split : IsSplitForcingSystem θ P π E
  order : IsOrderedSplitForcingSystem θ P R π E
  functions : IsFunctionalSplitForcingSystem θ P π E
  tops : IsToppedSplitForcingSystem θ P R π E t
  lifts : IsCoherentForcingLift θ P R π L
  compatible : IsSectionCompatibleForcingLift θ P R π E L

structure IsForcingIterationColumn (θ P R π E L t Q T ρ F M u : V) : Prop where
  split : IsSplitForcingColumn θ P π E Q ρ F
  order : IsOrderedSplitForcingColumn θ P R Q T ρ F
  functions : IsFunctionalSplitForcingColumn θ P Q ρ F
  tops : IsToppedSplitForcingColumn θ t Q T ρ F u
  lifts : IsCoherentForcingLiftColumn θ P R π L Q T ρ M
  compatible : IsSectionCompatibleLiftColumn θ P R π L F M

theorem IsForcingIterationSystem.extend {θ P R π E L t Q T ρ F M u : V}
    (h : IsForcingIterationSystem θ P R π E L t)
    (c : IsForcingIterationColumn θ P R π E L t Q T ρ F M u) :
    IsForcingIterationSystem (succ θ) (forcingFamilyNext θ P Q) (forcingFamilyNext θ R T)
      (forcingMatrixNext θ π ρ (identity Q)) (forcingMatrixNext θ E F (identity Q))
      (forcingMatrixNext θ L M (forcingIdentityLift Q)) (forcingFamilyNext θ t u) :=
  ⟨h.split.extend c.split, h.order.extend c.order, h.functions.extend c.functions,
    h.tops.extend c.tops, h.lifts.extend c.lifts, h.compatible.extend c.lifts c.compatible⟩

end ZFVP
