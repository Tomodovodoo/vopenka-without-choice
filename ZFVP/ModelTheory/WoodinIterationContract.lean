import ZFVP.ModelTheory.WoodinRecursionHistory
import ZFVP.ModelTheory.IterationQuotientClosure
import ZFVP.SetTheory.WoodinSeedCardinal

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- W02's fixed construction target for the restored-stage presentation.
The construction theorem is in WoodinConstruction. Source stage zero is
the trivial seed; recursive stage zero is its first restoration. -/
def WoodinIterationExit (δ : V) : Prop :=
  IsLeastDependentChoiceFailure (woodinSeedCardinal : V) ∧
  (∀ θ ∈ δ,
    IsWoodinIteration δ (succ θ) (kpair.π₁ (woodinIterationRec θ)) (kpair.π₂ (woodinIterationRec θ)) ∧
    HasWoodinQuotientClosure (succ θ) (kpair.π₁ (woodinIterationRec θ)) (kpair.π₂ (woodinIterationRec θ))) ∧
  IsWoodinIteration δ δ (woodinIterationPrefix δ) (woodinIterationCardinalPrefix δ) ∧
  HasWoodinQuotientClosure δ (woodinIterationPrefix δ) (woodinIterationCardinalPrefix δ)

/-- The restored-stage construction statement, proved by `woodinIterationConstruction`. -/
def WoodinIterationConstruction : Prop :=
  ∀ δ : V, IsWoodinSupercompact δ → ¬InternalChoice V → WoodinIterationExit δ

theorem woodinIteration_source_seed (hAC : ¬InternalChoice V) :
    IsLeastDependentChoiceFailure (woodinStageCardinal (woodinSeedStage : V)) ∧
      woodinStagePoset (woodinSeedStage : V) = {∅} := by
  simpa only [woodinSeedStage, woodinStageCardinal_code, woodinStagePoset_code] using
    And.intro (woodinSeedCardinal_spec hAC) (rfl : ({∅} : V) = {∅})

end ZFVP
