import ZFVP.ModelTheory.TwoStepBoundColumns
import ZFVP.ModelTheory.SuccessorBoundSections
import ZFVP.ModelTheory.ForcingSplitProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingComposeSectionColumn (θ F e : V) : V :=
  definableGraph θ (fun j ↦ compose (F ‘ j) e) (by definability)

theorem forcingComposeSectionColumn_value {θ F e j : V} (hj : j ∈ θ) :
    (forcingComposeSectionColumn θ F e) ‘ j = compose (F ‘ j) e :=
  value_definableGraph _ _ _ hj

theorem IsSectionCompatibleBoundColumn.twoStep {θ P R π B C T F M i I Q S one : V}
    (hc : IsSectionCompatibleBoundColumn θ P R π B F M i I)
    (hb : IsCoherentForcingBound θ P R π B i I)
    (hm : ∀ j ∈ θ, F ‘ j ∈ C ^ (P ‘ j))
    (hT : IsForcingPreorder C T) (htop : IsForcingTop C T one)
    (hQ : IsForcingIterand C T Q S ∅) :
    IsSectionCompatibleBoundColumn θ P R π B
      (forcingComposeSectionColumn θ F (twoStepSection C ∅))
      (forcingSuccessorBound (twoStepConditions C T Q ∅) (P ‘ i) (twoStepProjection C T Q ∅) M I) i I := by
  let D := twoStepConditions C T Q ∅
  let v := twoStepProjection C T Q ∅
  let e := twoStepSection C (∅ : V)
  have hs := twoStep_splitProjection hT htop hQ
  constructor
  intro j hj hij f hf p hp hbp
  rw [forcingComposeSectionColumn_value hj]
  have hF := hm j hj
  have hfe := compose_function hF hs.maps
  have hg := compose_function hf.1 hfe
  have he : compose (compose f (compose (F ‘ j) e)) v = compose f (F ‘ j) := by
    have hl := compose_function hg hs.projection.maps
    have hr := compose_function hf.1 hF
    let := IsFunction.of_mem hl
    let := IsFunction.of_mem hr
    apply functions_eq_of_domain_values
    · rw [domain_eq_of_mem_function hl, domain_eq_of_mem_function hr]
    · intro a ha
      rw [domain_eq_of_mem_function hl] at ha
      rw [value_compose_of_mem_function hg hs.projection.maps ha,
        value_compose_of_mem_function hf.1 hfe ha,
        value_compose_of_mem_function hF hs.maps (function_value_mem hf.1 ha),
        hs.right_inverse _ (function_value_mem hF (function_value_mem hf.1 ha)),
        value_compose_of_mem_function hf.1 hF ha]
  have ht : ∀ a ∈ I, kpair.π₂ ((compose f (compose (F ‘ j) e)) ‘ a) = ∅ := by
    intro a ha
    rw [value_compose_of_mem_function hf.1 hfe ha,
      value_compose_of_mem_function hF hs.maps (function_value_mem hf.1 ha),
      twoStepSection_value (function_value_mem hF (function_value_mem hf.1 ha)), kpair.π₂_kpair]
  rw [forcingSuccessorBound_value hg hp, twoStepUnionBound_empty_tails ht, he,
    hc.compatible j hj hij f hf p hp hbp,
    value_compose_of_mem_function hF hs.maps (hb.bound j hj hij f hf p hp hbp).1,
    twoStepSection_value (function_value_mem hF (hb.bound j hj hij f hf p hp hbp).1)]

end ZFVP
