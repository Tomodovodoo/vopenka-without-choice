import ZFVP.ModelTheory.TransportedLocalUnionBound
import ZFVP.ModelTheory.QuotientClosureComposition
import ZFVP.ModelTheory.ForcingProjectionComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext

theorem local_union_quotient_separative_bound (A : ForcingContext V) [Countable A.Model]
    {T U o τ E Q S t π δ p q : V}
    (hτ : IsForcingSplitProjection A.P A.R T U τ E)
    (hU : IsForcingPreorder T U) (ho : IsForcingTop T U o) (h : IsForcingIterand T U Q S t)
    (hπ : π ∈ A.P ^ twoStepConditions T U Q t)
    (he : ∀ c ∈ twoStepConditions T U Q t, τ ‘ (kpair.π₁ c) = π ‘ c)
    (f : ForcingName A.P) {α : A.Model} [IsOrdinal α]
    (hf : IsForcingDescending (A.projectionQuotient (twoStepConditions T U Q t) π)
      (forcingSeparativeOrder (A.projectionQuotient (twoStepConditions T U Q t) π)
        (A.projectionQuotientOrder (twoStepConditions T U Q t) (twoStepOrder T U Q S t) π)) α (A.ofName f))
    (hbound : ∀ i ∈ α,
      ⟨A.check q, (compose (A.ofName f) (A.check (twoStepProjection T U Q t))) ‘ i⟩ₖ ∈
        forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ))
    (hδ : IsChoicelessInaccessible δ) (hT : T ∈ hierarchy δ)
    (hp : p ∈ T) (hqp : ⟨q, p⟩ₖ ∈ U)
    (hDC : InternalDependentChoiceAt α)
    (hbase : IsForcingClosedThrough (A.projectionQuotient T τ)
      (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) α)
    (hcollapse : ∀ (H : Set V) (hH : IsExternalForcingGeneric T U H)
      (hA : forcingProjectionGeneric A.P A.R τ H = A.G),
      let C : ForcingContext V := ⟨T, U, o, H, hU, ho, hH⟩
      ∃ κ : C.Model, IsRegularCardinal κ ∧ κ ⊆ C.check δ ∧
        A.projectionInclusion C hτ hA α ∈ κ ∧
        C.ofName ⟨Q, h.posetName⟩ = woodinCollapse κ (C.check δ) ∧
        C.ofName ⟨S, h.orderName⟩ = woodinCollapseOrder κ (C.check δ))
    (hq : A.check ⟨q, forcingLocalCanonicalName T U o δ p
      (forcingSelectedUnion T U o (twoStepNames Q t) (twoStepTailSelector T U Q t) (nameAction E f.val))⟩ₖ ∈
        A.projectionQuotient (twoStepConditions T U Q t) π) :
    ∀ i ∈ α, ⟨A.check ⟨q, forcingLocalCanonicalName T U o δ p
      (forcingSelectedUnion T U o (twoStepNames Q t) (twoStepTailSelector T U Q t) (nameAction E f.val))⟩ₖ,
      (A.ofName f) ‘ i⟩ₖ ∈
      forcingSeparativeOrder (A.projectionQuotient (twoStepConditions T U Q t) π)
        (A.projectionQuotientOrder (twoStepConditions T U Q t) (twoStepOrder T U Q S t) π) := by
  have hρ := twoStep_projection hU ho h
  have heq : compose (twoStepProjection T U Q t) τ = π := by
    apply function_eq_of_values (compose_function hρ.maps hτ.projection.maps) hπ
    intro c hc
    rw [value_compose_of_mem_function hρ.maps hτ.projection.maps hc, twoStepProjection_value hc]
    exact he c hc
  have hπp : IsForcingProjection A.P A.R (twoStepConditions T U Q t) (twoStepOrder T U Q S t) π :=
    heq ▸ hτ.projection.comp hρ
  intro i hi
  apply A.projectionQuotient_separative_of_all_generics hπp (twoStep_preorder hU ho h)
    hq (function_value_mem hf.1 hi)
  intro G hG hAG hqG
  let C := twoStepFirstContext hU ho h hG
  have hA : forcingProjectionGeneric A.P A.R τ C.G = A.G := by
    change forcingProjectionGeneric A.P A.R τ
      (forcingProjectionGeneric T U (twoStepProjection T U Q t) G) = A.G
    rw [forcingProjectionGeneric_comp hτ.projection hρ A.order hU hG.1, heq, hAG]
  have hqC : q ∈ C.G := by
    have hx := hρ.image_mem hU hG.1 hqG
    rw [twoStepProjection_value (hG.1.1 _ hqG), kpair.π₁_kpair] at hx
    exact hx
  have hpC : p ∈ C.G := C.generic.1.2.2.1 q hqC p hp hqp
  obtain ⟨κ, hκ, hκδ, hακ, hQ, hS⟩ := hcollapse C.G C.generic hA
  exact A.transported_local_collapse_union_sequence C hτ hA h hπ he f hf hqC hbound
    hδ hT hpC hκ hκδ hακ
    (A.projectionInclusion_dependentChoiceAt_of_separative_closed C hτ hA hDC hbase)
    hQ hS hG rfl hqG i hi

end ForcingContext
end ZFVP
