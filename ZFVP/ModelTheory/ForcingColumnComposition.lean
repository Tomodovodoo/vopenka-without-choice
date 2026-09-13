import ZFVP.ModelTheory.TwoStepBoundSections

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsFunctionalSplitForcingColumn.comp {θ P C ρ F D v e : V}
    (m : IsFunctionalSplitForcingColumn θ P C ρ F) (hv : v ∈ C ^ D) (he : e ∈ D ^ C) :
    IsFunctionalSplitForcingColumn θ P D
      (forcingComposeProjectionColumn θ ρ v) (forcingComposeSectionColumn θ F e) := by
  constructor
  · intro i hi
    rw [forcingComposeProjectionColumn_value hi]
    exact compose_function hv (m.projection i hi)
  · intro i hi
    rw [forcingComposeSectionColumn_value hi]
    exact compose_function (m.sectionMap i hi) he

theorem IsSplitForcingColumn.comp {θ P π E C T ρ F D U v e : V}
    (h : IsSplitForcingSystem θ P π E) (c : IsSplitForcingColumn θ P π E C ρ F)
    (m : IsFunctionalSplitForcingColumn θ P C ρ F)
    (s : IsForcingSplitProjection C T D U v e) :
    IsSplitForcingColumn θ P π E D
      (forcingComposeProjectionColumn θ ρ v) (forcingComposeSectionColumn θ F e) := by
  constructor
  · intro i hi q hq
    rw [forcingComposeProjectionColumn_value hi,
      value_compose_of_mem_function s.projection.maps (m.projection i hi) hq]
    exact c.projMaps i hi _ (function_value_mem s.projection.maps hq)
  · intro i hi p hp
    rw [forcingComposeSectionColumn_value hi,
      value_compose_of_mem_function (m.sectionMap i hi) s.maps hp]
    exact function_value_mem s.maps (c.secMaps i hi p hp)
  · intro i hi j hj hij q hq
    rw [forcingComposeProjectionColumn_value hi, forcingComposeProjectionColumn_value hj,
      value_compose_of_mem_function s.projection.maps (m.projection i hi) hq,
      value_compose_of_mem_function s.projection.maps (m.projection j hj) hq]
    exact c.projComp i hi j hj hij _ (function_value_mem s.projection.maps hq)
  · intro i hi j hj hij p hp
    rw [forcingComposeSectionColumn_value hi, forcingComposeSectionColumn_value hj,
      value_compose_of_mem_function (m.sectionMap i hi) s.maps hp,
      value_compose_of_mem_function (m.sectionMap j hj) s.maps (h.secMaps i hi j hj hij p hp),
      c.secComp i hi j hj hij p hp]
  · intro i hi p hp
    rw [forcingComposeProjectionColumn_value hi, forcingComposeSectionColumn_value hi,
      value_compose_of_mem_function s.projection.maps (m.projection i hi)
        (function_value_mem (compose_function (m.sectionMap i hi) s.maps) hp),
      value_compose_of_mem_function (m.sectionMap i hi) s.maps hp,
      s.right_inverse _ (c.secMaps i hi p hp), c.retraction i hi p hp]

theorem IsOrderedSplitForcingColumn.comp {θ P R C T ρ F D U v e : V}
    (c : IsOrderedSplitForcingColumn θ P R C T ρ F)
    (m : IsFunctionalSplitForcingColumn θ P C ρ F)
    (s : IsForcingSplitProjection C T D U v e) (hU : IsForcingPreorder D U) :
    IsOrderedSplitForcingColumn θ P R D U
      (forcingComposeProjectionColumn θ ρ v) (forcingComposeSectionColumn θ F e) := by
  refine ⟨hU, ?_, ?_⟩
  · intro i hi a ha b hb hab
    rw [forcingComposeProjectionColumn_value hi,
      value_compose_of_mem_function s.projection.maps (m.projection i hi) ha,
      value_compose_of_mem_function s.projection.maps (m.projection i hi) hb]
    exact c.projMono i hi _ (function_value_mem s.projection.maps ha) _
      (function_value_mem s.projection.maps hb) (s.projection.monotone a ha b hb hab)
  · intro i hi a ha b hb
    rw [forcingComposeProjectionColumn_value hi, forcingComposeSectionColumn_value hi,
      value_compose_of_mem_function s.projection.maps (m.projection i hi) ha,
      value_compose_of_mem_function (m.sectionMap i hi) s.maps hb,
      s.below a ha _ (function_value_mem (m.sectionMap i hi) hb)]
    exact c.below i hi _ (function_value_mem s.projection.maps ha) b hb

end ZFVP
