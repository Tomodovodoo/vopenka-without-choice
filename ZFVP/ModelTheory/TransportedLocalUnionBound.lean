import ZFVP.ModelTheory.TransportedTwoStepSequence
import ZFVP.ModelTheory.TwoStepLocalUnionBound

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext

theorem transported_local_collapse_union_bound (A C : ForcingContext V)
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
      (A.ofName f) ‘ i = A.check c → kpair.π₁ c ∈ C.G)
    {δ p : V} (hδ : IsChoicelessInaccessible δ) (hP : C.P ∈ hierarchy δ) (hp : p ∈ C.G)
    {κ : C.Model} (hκ : IsRegularCardinal κ) (hκδ : κ ⊆ C.check δ)
    (hακ : A.projectionInclusion C hτ hA α ∈ κ)
    (hDC : InternalDependentChoiceAt (A.projectionInclusion C hτ hA α))
    (hQ : C.ofName ⟨Q, h.posetName⟩ = woodinCollapse κ (C.check δ))
    (hS : C.ofName ⟨S, h.orderName⟩ = woodinCollapseOrder κ (C.check δ)) :
    let g := nameAction E f.val
    let ν := forcingLocalCanonicalName C.P C.R C.one δ p
      (forcingSelectedUnion C.P C.R C.one (twoStepNames Q t) (twoStepTailSelector C.P C.R Q t) g)
    let u := C.ofName ⟨ν, forcingLocalCanonicalName_isName _ _ _ _ _ _⟩
    u ∈ C.ofName ⟨Q, h.posetName⟩ ∧ ∀ j ∈ A.projectionInclusion C hτ hA α,
      ⟨u, (compose (compose (C.ofName ⟨g, nameAction_isName hτ.maps f.property⟩)
        (C.check (twoStepTailSelector C.P C.R Q t)))
        (C.evaluationGraph (twoStepNames Q t) (fun _ hν ↦ h.name hν))) ‘ j⟩ₖ ∈
          C.ofName ⟨S, h.orderName⟩ := by
  let := hκ.1.1
  let := IsOrdinal.of_mem hακ
  exact TwoStepModel.local_collapse_union_bound C h hδ hP hp
    ⟨nameAction E f.val, nameAction_isName hτ.maps f.property⟩
    (A.transported_twoStep_quotient_descending C hτ hA h hπ he f hf hfirst) hκ hκδ hακ hDC hQ hS

theorem transported_local_collapse_union_bound_of_bound (A C : ForcingContext V)
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
        forcingSeparativeOrder (A.projectionQuotient C.P τ) (A.projectionQuotientOrder C.P C.R τ))
    {δ p : V} (hδ : IsChoicelessInaccessible δ) (hP : C.P ∈ hierarchy δ) (hp : p ∈ C.G)
    {κ : C.Model} (hκ : IsRegularCardinal κ) (hκδ : κ ⊆ C.check δ)
    (hακ : A.projectionInclusion C hτ hA α ∈ κ)
    (hDC : InternalDependentChoiceAt (A.projectionInclusion C hτ hA α))
    (hQ : C.ofName ⟨Q, h.posetName⟩ = woodinCollapse κ (C.check δ))
    (hS : C.ofName ⟨S, h.orderName⟩ = woodinCollapseOrder κ (C.check δ)) :
    let g := nameAction E f.val
    let ν := forcingLocalCanonicalName C.P C.R C.one δ p
      (forcingSelectedUnion C.P C.R C.one (twoStepNames Q t) (twoStepTailSelector C.P C.R Q t) g)
    let u := C.ofName ⟨ν, forcingLocalCanonicalName_isName _ _ _ _ _ _⟩
    u ∈ C.ofName ⟨Q, h.posetName⟩ ∧ ∀ j ∈ A.projectionInclusion C hτ hA α,
      ⟨u, (compose (compose (C.ofName ⟨g, nameAction_isName hτ.maps f.property⟩)
        (C.check (twoStepTailSelector C.P C.R Q t)))
        (C.evaluationGraph (twoStepNames Q t) (fun _ hν ↦ h.name hν))) ‘ j⟩ₖ ∈
          C.ofName ⟨S, h.orderName⟩ := by
  let := hκ.1.1
  let := IsOrdinal.of_mem hακ
  exact TwoStepModel.local_collapse_union_bound C h hδ hP hp
    ⟨nameAction E f.val, nameAction_isName hτ.maps f.property⟩
    (A.transported_twoStep_quotient_descending_of_bound C hτ hA h hπ he f hf hq hbound) hκ hκδ hακ hDC hQ hS

theorem transported_local_collapse_union_sequence (A C : ForcingContext V)
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
        forcingSeparativeOrder (A.projectionQuotient C.P τ) (A.projectionQuotientOrder C.P C.R τ))
    {δ p : V} (hδ : IsChoicelessInaccessible δ) (hP : C.P ∈ hierarchy δ) (hp : p ∈ C.G)
    {κ : C.Model} (hκ : IsRegularCardinal κ) (hκδ : κ ⊆ C.check δ)
    (hακ : A.projectionInclusion C hτ hA α ∈ κ)
    (hDC : InternalDependentChoiceAt (A.projectionInclusion C hτ hA α))
    (hQ : C.ofName ⟨Q, h.posetName⟩ = woodinCollapse κ (C.check δ))
    (hS : C.ofName ⟨S, h.orderName⟩ = woodinCollapseOrder κ (C.check δ))
    {G : Set V} (hG : IsExternalForcingGeneric
      (twoStepConditions C.P C.R Q t) (twoStepOrder C.P C.R Q S t) G)
    (hC : C.G = forcingProjectionGeneric C.P C.R (twoStepProjection C.P C.R Q t) G)
    (hpair : ⟨q, forcingLocalCanonicalName C.P C.R C.one δ p
      (forcingSelectedUnion C.P C.R C.one (twoStepNames Q t)
        (twoStepTailSelector C.P C.R Q t) (nameAction E f.val))⟩ₖ ∈ G) :
    ∀ i ∈ α, (A.ofName f) ‘ i ∈ A.projectionQuotientFilter G := by
  let := hκ.1.1
  let := IsOrdinal.of_mem hακ
  have hm := TwoStepModel.mem_of_local_collapse_union C h hδ hP hp
    ⟨nameAction E f.val, nameAction_isName hτ.maps f.property⟩
    (A.transported_twoStep_quotient_descending_of_bound C hτ hA h hπ he f hf hq hbound)
    hκ hκδ hακ hDC hQ hS hG hC hpair
  intro i hi
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
