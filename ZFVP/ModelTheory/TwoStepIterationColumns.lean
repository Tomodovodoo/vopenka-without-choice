import ZFVP.ModelTheory.TwoStepLiftColumns
import ZFVP.SetTheory.ForcingIterationSystem

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsSectionCompatibleLiftColumn.twoStep {θ P R π L C T F M Q S t one : V}
    (c : IsSectionCompatibleLiftColumn θ P R π L F M)
    (hL : IsCoherentForcingLift θ P R π L)
    (hm : ∀ j ∈ θ, F ‘ j ∈ C ^ (P ‘ j))
    (hT : IsForcingPreorder C T) (htop : IsForcingTop C T one)
    (hQ : IsForcingIterand C T Q S t) :
    IsSectionCompatibleLiftColumn θ P R π L
      (forcingComposeSectionColumn θ F (twoStepSection C t))
      (forcingTwoStepLiftColumn θ (twoStepConditions C T Q t) P M) := by
  have hs := twoStep_splitProjection hT htop hQ
  constructor
  intro i hi j hj hij a ha b hb hle
  have hq := (hL.lift i hi j hj hij a ha b hb hle).1
  rw [forcingComposeSectionColumn_value hj]
  have hfa := function_value_mem (hm j hj) ha
  have hea := function_value_mem (compose_function (hm j hj) hs.maps) ha
  rw [forcingTwoStepLiftColumn_value hi hea hb,
    value_compose_of_mem_function (hm j hj) hs.maps ha,
    value_compose_of_mem_function (hm j hj) hs.maps hq,
    twoStepSection_value hfa,
    twoStepSection_value (function_value_mem (hm j hj) hq), successorForcingLift_section,
    c.compatible i hi j hj hij a ha b hb hle]

theorem IsToppedSplitForcingColumn.twoStep {θ P t C T ρ F one Q S u : V}
    (c : IsToppedSplitForcingColumn θ t C T ρ F one)
    (hm : IsFunctionalSplitForcingColumn θ P C ρ F)
    (ht : ∀ i ∈ θ, t ‘ i ∈ P ‘ i)
    (hT : IsForcingPreorder C T) (hQ : IsForcingIterand C T Q S u) :
    IsToppedSplitForcingColumn θ t (twoStepConditions C T Q u) (twoStepOrder C T Q S u)
      (forcingComposeProjectionColumn θ ρ (twoStepProjection C T Q u))
      (forcingComposeSectionColumn θ F (twoStepSection C u)) ⟨one, u⟩ₖ := by
  have hs := twoStep_splitProjection hT c.top hQ
  have ht' := twoStep_top hT c.top hQ
  refine ⟨ht', ?_, ?_⟩
  · intro i hi
    rw [forcingComposeProjectionColumn_twoStep_value hi (hm.projection i hi) hT c.top hQ ht'.1,
      kpair.π₁_kpair, c.projTop i hi]
  · intro i hi
    rw [forcingComposeSectionColumn_value hi,
      value_compose_of_mem_function (hm.sectionMap i hi) hs.maps (ht i hi),
      c.secTop i hi, twoStepSection_value c.top.1]

theorem IsForcingIterationColumn.twoStep {θ P R π E L t C T ρ F M one Q S u : V}
    (h : IsForcingIterationSystem θ P R π E L t)
    (c : IsForcingIterationColumn θ P R π E L t C T ρ F M one)
    (hQ : IsForcingIterand C T Q S u) :
    IsForcingIterationColumn θ P R π E L t
      (twoStepConditions C T Q u) (twoStepOrder C T Q S u)
      (forcingComposeProjectionColumn θ ρ (twoStepProjection C T Q u))
      (forcingComposeSectionColumn θ F (twoStepSection C u))
      (forcingTwoStepLiftColumn θ (twoStepConditions C T Q u) P M) ⟨one, u⟩ₖ := by
  have hs := twoStep_splitProjection c.order.preorder c.tops.top hQ
  exact ⟨c.split.comp h.split c.functions hs,
    c.order.comp c.functions hs (twoStep_preorder c.order.preorder c.tops.top hQ),
    c.functions.comp hs.projection.maps hs.maps,
    c.tops.twoStep c.functions (fun i hi ↦ (h.tops.top i hi).1) c.order.preorder hQ,
    c.lifts.twoStep c.functions.projection c.order.preorder c.tops.top hQ,
    c.compatible.twoStep h.lifts c.functions.sectionMap c.order.preorder c.tops.top hQ⟩

end ZFVP

