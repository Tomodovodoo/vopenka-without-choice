import ZFVP.SetTheory.EndExtensionHierarchyAgreement
import ZFVP.ModelTheory.UsubaTransportedLocalUnion
import ZFVP.ModelTheory.TwoStepUsubaLocalUnion
import ZFVP.ModelTheory.ForcingProjectionComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext

theorem usuba_local_union_quotient_separative_bound (A : ForcingContext V) [Countable A.Model]
    {T U o τ E π p q : V}
    (hτ : IsForcingSplitProjection A.P A.R T U τ E)
    (hU : IsForcingPreorder T U) (ho : IsForcingTop T U o)
    (hπ : π ∈ A.P ^ twoStepConditions T U (usubaSaturatedPosetName T U) ∅)
    (he : ∀ c ∈ twoStepConditions T U (usubaSaturatedPosetName T U) ∅,
      τ ‘ (kpair.π₁ c) = π ‘ c)
    (f : ForcingName A.P) {α : A.Model} [IsOrdinal α]
    (hf : IsForcingDescending (A.projectionQuotient (twoStepConditions T U (usubaSaturatedPosetName T U) ∅) π)
      (forcingSeparativeOrder (A.projectionQuotient (twoStepConditions T U (usubaSaturatedPosetName T U) ∅) π)
        (A.projectionQuotientOrder (twoStepConditions T U (usubaSaturatedPosetName T U) ∅)
          (twoStepOrder T U (usubaSaturatedPosetName T U)
            (reverseInclusionOrderName T U (usubaSaturatedPosetName T U)) ∅) π)) α (A.ofName f))
    (hbound : ∀ i ∈ α,
      ⟨A.check q, (compose (A.ofName f)
        (A.check (twoStepProjection T U (usubaSaturatedPosetName T U) ∅))) ‘ i⟩ₖ ∈
          forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ))
    (hp : p ∈ T) (hqp : ⟨q, p⟩ₖ ∈ U)
    (hDC : InternalDependentChoiceAt α)
    (hbase : IsForcingClosedThrough (A.projectionQuotient T τ)
      (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) α)
    (hq : A.check ⟨q, usubaLocalUnionName T U o p (nameAction E f.val)⟩ₖ ∈
      A.projectionQuotient (twoStepConditions T U (usubaSaturatedPosetName T U) ∅) π) :
    ∀ i ∈ α, ⟨A.check ⟨q, usubaLocalUnionName T U o p (nameAction E f.val)⟩ₖ,
      (A.ofName f) ‘ i⟩ₖ ∈
      forcingSeparativeOrder (A.projectionQuotient (twoStepConditions T U (usubaSaturatedPosetName T U) ∅) π)
        (A.projectionQuotientOrder (twoStepConditions T U (usubaSaturatedPosetName T U) ∅)
          (twoStepOrder T U (usubaSaturatedPosetName T U)
            (reverseInclusionOrderName T U (usubaSaturatedPosetName T U)) ∅) π) := by
  let Q := usubaSaturatedPosetName T U
  let S := reverseInclusionOrderName T U Q
  let h := usubaSaturated_iterand hU ho
  have hρ := twoStep_projection hU ho h
  have heq : compose (twoStepProjection T U Q ∅) τ = π := by
    apply function_eq_of_values (compose_function hρ.maps hτ.projection.maps) hπ
    intro c hc
    rw [value_compose_of_mem_function hρ.maps hτ.projection.maps hc, twoStepProjection_value hc]
    exact he c hc
  have hπp : IsForcingProjection A.P A.R (twoStepConditions T U Q ∅) (twoStepOrder T U Q S ∅) π :=
    heq ▸ hτ.projection.comp hρ
  intro i hi
  apply A.projectionQuotient_separative_of_all_generics hπp (twoStep_preorder hU ho h)
    hq (function_value_mem hf.1 hi)
  intro G hG hAG hqG
  let C := twoStepFirstContext hU ho h hG
  have hA : forcingProjectionGeneric A.P A.R τ C.G = A.G := by
    change forcingProjectionGeneric A.P A.R τ
      (forcingProjectionGeneric T U (twoStepProjection T U Q ∅) G) = A.G
    rw [forcingProjectionGeneric_comp hτ.projection hρ A.order hU hG.1, heq, hAG]
  have hqC : q ∈ C.G := by
    have hx := hρ.image_mem hU hG.1 hqG
    rw [twoStepProjection_value (hG.1.1 _ hqG), kpair.π₁_kpair] at hx
    exact hx
  have hpC : p ∈ C.G := C.generic.1.2.2.1 q hqC p hp hqp
  have hd := A.transported_twoStep_quotient_descending_of_bound C hτ hA h hπ he f hf hqC hbound
  have hdc := A.projectionInclusion_dependentChoiceAt_of_separative_closed C hτ hA hDC hbase
  let := ((A.projectionInclusion C hτ hA).ordinal_iff α).mpr (inferInstance : IsOrdinal α)
  have hm := TwoStepModel.mem_of_local_usuba_union C hpC
    ⟨nameAction E f.val, nameAction_isName hτ.maps f.property⟩ hd hdc hG rfl hqG
  have hv := hm (A.projectionInclusion C hτ hA i)
    ((A.projectionInclusion C hτ hA).mem_iff i α |>.mpr hi)
  rw [A.projectionInclusion_nameAction C hτ hA f,
    ← (A.projectionInclusion C hτ hA).map_value_total] at hv
  obtain ⟨c, hc, _, hci⟩ := (A.mem_projectionQuotient_iff hπ _).mp (function_value_mem hf.1 hi)
  rw [hci, A.projectionInclusion_check C hτ hA] at hv
  obtain ⟨d, hd, hcd⟩ := hv
  exact ⟨d, hd, hci.trans (congrArg A.check ((C.check_eq_iff _ _).mp hcd))⟩

end ForcingContext
end ZFVP
