import ZFVP.ModelTheory.QuotientSeparativeTower
import ZFVP.ModelTheory.TwoStepSelectedDescending
import ZFVP.ModelTheory.ProjectionNameTransport
import ZFVP.ModelTheory.ProjectionGenericBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext

theorem transported_twoStep_quotient_descending (A C : ForcingContext V)
    {Q S t π τ E : V} {α : A.Model} [IsOrdinal α]
    (hτ : IsForcingSplitProjection A.P A.R C.P C.R τ E)
    (hA : forcingProjectionGeneric A.P A.R τ C.G = A.G)
    (h : IsForcingIterand C.P C.R Q S t)
    (hπ : π ∈ A.P ^ twoStepConditions C.P C.R Q t)
    (he : ∀ c ∈ twoStepConditions C.P C.R Q t, τ ‘ (kpair.π₁ c) = π ‘ c)
    (f : ForcingName A.P)
    (hf : IsForcingDescending (A.projectionQuotient (twoStepConditions C.P C.R Q t) π)
      (forcingSeparativeOrder (A.projectionQuotient (twoStepConditions C.P C.R Q t) π)
        (A.projectionQuotientOrder (twoStepConditions C.P C.R Q t) (twoStepOrder C.P C.R Q S t) π))
      α (A.ofName f))
    (hfirst : ∀ i ∈ α, ∀ c ∈ twoStepConditions C.P C.R Q t,
      (A.ofName f) ‘ i = A.check c → kpair.π₁ c ∈ C.G) :
    IsForcingDescending
      (C.projectionQuotient (twoStepConditions C.P C.R Q t) (twoStepProjection C.P C.R Q t))
      (forcingSeparativeOrder
        (C.projectionQuotient (twoStepConditions C.P C.R Q t) (twoStepProjection C.P C.R Q t))
        (C.projectionQuotientOrder (twoStepConditions C.P C.R Q t) (twoStepOrder C.P C.R Q S t)
          (twoStepProjection C.P C.R Q t)))
      (A.projectionInclusion C hτ hA α)
      (C.ofName ⟨nameAction E f.val, nameAction_isName hτ.maps f.property⟩) := by
  rw [A.projectionInclusion_nameAction C hτ hA f]
  refine A.projectionQuotient_descending_tower C hτ hA hπ
    (twoStep_projection C.order C.top h) (twoStep_preorder C.order C.top h) ?_ hf ?_
  · intro c hc
    rw [twoStepProjection_value hc]
    exact he c hc
  · intro i hi c hc hci
    rw [twoStepProjection_value hc]
    exact hfirst i hi c hc hci

theorem transported_twoStep_quotient_descending_of_bound (A C : ForcingContext V)
    {Q S t π τ E : V} {α : A.Model} [IsOrdinal α]
    (hτ : IsForcingSplitProjection A.P A.R C.P C.R τ E)
    (hA : forcingProjectionGeneric A.P A.R τ C.G = A.G)
    (h : IsForcingIterand C.P C.R Q S t)
    (hπ : π ∈ A.P ^ twoStepConditions C.P C.R Q t)
    (he : ∀ c ∈ twoStepConditions C.P C.R Q t, τ ‘ (kpair.π₁ c) = π ‘ c)
    (f : ForcingName A.P)
    (hf : IsForcingDescending (A.projectionQuotient (twoStepConditions C.P C.R Q t) π)
      (forcingSeparativeOrder (A.projectionQuotient (twoStepConditions C.P C.R Q t) π)
        (A.projectionQuotientOrder (twoStepConditions C.P C.R Q t) (twoStepOrder C.P C.R Q S t) π))
      α (A.ofName f))
    {q : V} (hq : q ∈ C.G)
    (hbound : ∀ i ∈ α,
      ⟨A.check q, (compose (A.ofName f) (A.check (twoStepProjection C.P C.R Q t))) ‘ i⟩ₖ ∈
        forcingSeparativeOrder (A.projectionQuotient C.P τ) (A.projectionQuotientOrder C.P C.R τ)) :
    IsForcingDescending
      (C.projectionQuotient (twoStepConditions C.P C.R Q t) (twoStepProjection C.P C.R Q t))
      (forcingSeparativeOrder
        (C.projectionQuotient (twoStepConditions C.P C.R Q t) (twoStepProjection C.P C.R Q t))
        (C.projectionQuotientOrder (twoStepConditions C.P C.R Q t) (twoStepOrder C.P C.R Q S t)
          (twoStepProjection C.P C.R Q t)))
      (A.projectionInclusion C hτ hA α)
      (C.ofName ⟨nameAction E f.val, nameAction_isName hτ.maps f.property⟩) := by
  apply A.transported_twoStep_quotient_descending C hτ hA h hπ he f hf
  intro i hi c hc hci
  have hρ := twoStepProjection_maps C.P C.R Q t
  let := IsFunction.of_mem hρ
  have hfc := mem_function_of_mem_function_of_subset hf.1 sep_subset
  have hb := hbound i hi
  rw [value_compose_of_mem_function hfc ((A.check_function_iff _ _ _).mpr hρ) hi, hci,
    A.check_value ((domain_eq_of_mem_function hρ).symm ▸ hc), twoStepProjection_value hc] at hb
  obtain ⟨d, hd, hed⟩ := externalForcingGeneric_separative_upward
    (A.projectionQuotient_preorder hτ.projection.maps C.order)
    (A.projectionQuotient_generic hτ C.order C.generic hA) (show A.check q ∈ A.projectionQuotientFilter C.G from ⟨q, hq, rfl⟩) hb
  exact ((A.check_eq_iff _ _).mp hed) ▸ hd

theorem transported_twoStep_tail_descending (A C : ForcingContext V)
    {Q S t π τ E : V} {α : A.Model} [IsOrdinal α]
    (hτ : IsForcingSplitProjection A.P A.R C.P C.R τ E)
    (hA : forcingProjectionGeneric A.P A.R τ C.G = A.G)
    (h : IsForcingIterand C.P C.R Q S t)
    (hπ : π ∈ A.P ^ twoStepConditions C.P C.R Q t)
    (he : ∀ c ∈ twoStepConditions C.P C.R Q t, τ ‘ (kpair.π₁ c) = π ‘ c)
    (f : ForcingName A.P)
    (hf : IsForcingDescending (A.projectionQuotient (twoStepConditions C.P C.R Q t) π)
      (forcingSeparativeOrder (A.projectionQuotient (twoStepConditions C.P C.R Q t) π)
        (A.projectionQuotientOrder (twoStepConditions C.P C.R Q t) (twoStepOrder C.P C.R Q S t) π))
      α (A.ofName f))
    (hfirst : ∀ i ∈ α, ∀ c ∈ twoStepConditions C.P C.R Q t,
      (A.ofName f) ‘ i = A.check c → kpair.π₁ c ∈ C.G) :
    IsForcingDescending (C.ofName ⟨Q, h.posetName⟩)
      (forcingSeparativeOrder (C.ofName ⟨Q, h.posetName⟩) (C.ofName ⟨S, h.orderName⟩))
      (A.projectionInclusion C hτ hA α)
      (compose (compose (C.ofName ⟨nameAction E f.val, nameAction_isName hτ.maps f.property⟩)
        (C.check (twoStepTailSelector C.P C.R Q t)))
        (C.evaluationGraph (twoStepNames Q t) (fun _ hν ↦ h.name hν))) := by
  let j := A.projectionInclusion C hτ hA
  have ho : IsOrdinal (j α) :=
    (j.bounded_defined isOrdinalFormula_bounded (fun v ↦ IsOrdinal (v 0))
      (fun v ↦ IsOrdinal (v 0)) ![α]).mp (show IsOrdinal α from inferInstance)
  let := ho
  exact TwoStepModel.selected_tail_descending C h
    (A.transported_twoStep_quotient_descending C hτ hA h hπ he f hf hfirst)

end ForcingContext
end ZFVP
