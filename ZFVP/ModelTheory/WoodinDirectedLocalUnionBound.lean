import ZFVP.ModelTheory.WoodinDirectedTwoStepBounds
import ZFVP.ModelTheory.LocalUnionQuotientBound

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext

theorem transported_local_collapse_directed_union_bound (A C : ForcingContext V)
    {Q S t π τ E : V} {α : A.Model} [IsOrdinal α]
    (hτ : IsForcingSplitProjection A.P A.R C.P C.R τ E)
    (hA : forcingProjectionGeneric A.P A.R τ C.G = A.G)
    (h : IsForcingIterand C.P C.R Q S t)
    (hπ : π ∈ A.P ^ twoStepConditions C.P C.R Q t)
    (he : ∀ c ∈ twoStepConditions C.P C.R Q t, τ ‘ (kpair.π₁ c) = π ‘ c)
    (f : ForcingName A.P)
    (hf : IsForcingDirectedFamily (A.projectionQuotient (twoStepConditions C.P C.R Q t) π)
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
  exact TwoStepModel.local_collapse_directed_union_bound C h hδ hP hp
    ⟨nameAction E f.val, nameAction_isName hτ.maps f.property⟩
    (A.transported_twoStep_quotient_directed C hτ hA h hπ he f hf hfirst) hκ hκδ hακ hDC hQ hS

theorem transported_local_collapse_directed_union_bound_of_bound (A C : ForcingContext V)
    {Q S t π τ E : V} {α : A.Model} [IsOrdinal α]
    (hτ : IsForcingSplitProjection A.P A.R C.P C.R τ E)
    (hA : forcingProjectionGeneric A.P A.R τ C.G = A.G)
    (h : IsForcingIterand C.P C.R Q S t)
    (hπ : π ∈ A.P ^ twoStepConditions C.P C.R Q t)
    (he : ∀ c ∈ twoStepConditions C.P C.R Q t, τ ‘ (kpair.π₁ c) = π ‘ c)
    (f : ForcingName A.P)
    (hf : IsForcingDirectedFamily (A.projectionQuotient (twoStepConditions C.P C.R Q t) π)
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
  exact TwoStepModel.local_collapse_directed_union_bound C h hδ hP hp
    ⟨nameAction E f.val, nameAction_isName hτ.maps f.property⟩
    (A.transported_twoStep_quotient_directed_of_bound C hτ hA h hπ he f hf hq hbound) hκ hκδ hακ hDC hQ hS

theorem transported_local_collapse_directed_union_sequence (A C : ForcingContext V)
    {Q S t π τ E : V} {α : A.Model} [IsOrdinal α]
    (hτ : IsForcingSplitProjection A.P A.R C.P C.R τ E)
    (hA : forcingProjectionGeneric A.P A.R τ C.G = A.G)
    (h : IsForcingIterand C.P C.R Q S t)
    (hπ : π ∈ A.P ^ twoStepConditions C.P C.R Q t)
    (he : ∀ c ∈ twoStepConditions C.P C.R Q t, τ ‘ (kpair.π₁ c) = π ‘ c)
    (f : ForcingName A.P)
    (hf : IsForcingDirectedFamily (A.projectionQuotient (twoStepConditions C.P C.R Q t) π)
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
  have hm := TwoStepModel.mem_of_local_collapse_directed_union C h hδ hP hp
    ⟨nameAction E f.val, nameAction_isName hτ.maps f.property⟩
    (A.transported_twoStep_quotient_directed_of_bound C hτ hA h hπ he f hf hq hbound)
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

theorem local_directed_union_quotient_separative_bound (A : ForcingContext V) [Countable A.Model]
    {T U o τ E Q S t π δ p q : V}
    (hτ : IsForcingSplitProjection A.P A.R T U τ E)
    (hU : IsForcingPreorder T U) (ho : IsForcingTop T U o) (h : IsForcingIterand T U Q S t)
    (hπ : π ∈ A.P ^ twoStepConditions T U Q t)
    (he : ∀ c ∈ twoStepConditions T U Q t, τ ‘ (kpair.π₁ c) = π ‘ c)
    (f : ForcingName A.P) {α : A.Model} [IsOrdinal α]
    (hf : IsForcingDirectedFamily (A.projectionQuotient (twoStepConditions T U Q t) π)
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
  exact A.transported_local_collapse_directed_union_sequence C hτ hA h hπ he f hf hqC hbound
    hδ hT hpC hκ hκδ hακ
    (A.projectionInclusion_dependentChoiceAt_of_separative_closed C hτ hA hDC hbase)
    hQ hS hG rfl hqG i hi

end ForcingContext
end ZFVP
