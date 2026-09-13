import ZFVP.ModelTheory.WoodinDirectedQuotientBounds
import ZFVP.ModelTheory.TransportedTwoStepSequence
import ZFVP.ModelTheory.TwoStepLocalUnionBound
import ZFVP.ModelTheory.TwoStepQuotientClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TwoStepModel

theorem selected_tail_directed (A : ForcingContext V) {Q S t : V}
    (h : IsForcingIterand A.P A.R Q S t) {α f : A.Model}
    (hf : IsForcingDirectedFamily
      (A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t))
      (forcingSeparativeOrder
        (A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t))
        (A.projectionQuotientOrder (twoStepConditions A.P A.R Q t)
          (twoStepOrder A.P A.R Q S t) (twoStepProjection A.P A.R Q t))) α f) :
    IsForcingDirectedFamily (A.ofName ⟨Q, h.posetName⟩)
      (forcingSeparativeOrder (A.ofName ⟨Q, h.posetName⟩) (A.ofName ⟨S, h.orderName⟩)) α
      (compose (compose f (A.check (twoStepTailSelector A.P A.R Q t)))
        (A.evaluationGraph (twoStepNames Q t) (fun _ hτ ↦ h.name hτ))) := by
  rw [selected_tail_sequence_eq A h hf.1]
  exact (A.twoStepQuotientProjection_projection h).separative_directed_compose hf

variable (A : ForcingContext V) {Q S t : V} (h : IsForcingIterand A.P A.R Q S t)

theorem local_collapse_directed_union_bound {δ p : V}
    (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ) (hp : p ∈ A.G)
    (f : ForcingName A.P) {κ α : A.Model} [IsOrdinal α]
    (hf : IsForcingDirectedFamily
      (A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t))
      (forcingSeparativeOrder
        (A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t))
        (A.projectionQuotientOrder (twoStepConditions A.P A.R Q t)
          (twoStepOrder A.P A.R Q S t) (twoStepProjection A.P A.R Q t))) α (A.ofName f))
    (hκ : IsRegularCardinal κ) (hκδ : κ ⊆ A.check δ)
    (hα : α ∈ κ) (hDC : InternalDependentChoiceAt α)
    (hQ : A.ofName ⟨Q, h.posetName⟩ = woodinCollapse κ (A.check δ))
    (hS : A.ofName ⟨S, h.orderName⟩ = woodinCollapseOrder κ (A.check δ)) :
    let ν := forcingLocalCanonicalName A.P A.R A.one δ p
      (forcingSelectedUnion A.P A.R A.one (twoStepNames Q t) (twoStepTailSelector A.P A.R Q t) f.val)
    let u := A.ofName ⟨ν, forcingLocalCanonicalName_isName _ _ _ _ _ _⟩
    u ∈ A.ofName ⟨Q, h.posetName⟩ ∧ ∀ i ∈ α,
      ⟨u, (compose (compose (A.ofName f) (A.check (twoStepTailSelector A.P A.R Q t)))
        (A.evaluationGraph (twoStepNames Q t) (fun _ hτ ↦ h.name hτ))) ‘ i⟩ₖ ∈
          A.ofName ⟨S, h.orderName⟩ := by
  have hs := selected_tail_directed A h hf
  rw [hQ, hS] at hs ⊢
  exact A.localSelectedUnion_collapse_directed_bound hδ hP hp (fun _ hτ ↦ h.name hτ)
    (twoStepTailSelector_maps A.P A.R Q t) f
    (mem_function_of_mem_function_of_subset hf.1 sep_subset) hκ hκδ hα hDC hs

theorem mem_of_local_collapse_directed_union {δ p q : V}
    (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ) (hp : p ∈ A.G)
    (f : ForcingName A.P) {κ α : A.Model} [IsOrdinal α]
    (hf : IsForcingDirectedFamily
      (A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t))
      (forcingSeparativeOrder
        (A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t))
        (A.projectionQuotientOrder (twoStepConditions A.P A.R Q t)
          (twoStepOrder A.P A.R Q S t) (twoStepProjection A.P A.R Q t))) α (A.ofName f))
    (hκ : IsRegularCardinal κ) (hκδ : κ ⊆ A.check δ)
    (hα : α ∈ κ) (hDC : InternalDependentChoiceAt α)
    (hQ : A.ofName ⟨Q, h.posetName⟩ = woodinCollapse κ (A.check δ))
    (hS : A.ofName ⟨S, h.orderName⟩ = woodinCollapseOrder κ (A.check δ))
    {G : Set V} (hG : IsExternalForcingGeneric
      (twoStepConditions A.P A.R Q t) (twoStepOrder A.P A.R Q S t) G)
    (hA : A.G = forcingProjectionGeneric A.P A.R (twoStepProjection A.P A.R Q t) G)
    (hq : ⟨q, forcingLocalCanonicalName A.P A.R A.one δ p
      (forcingSelectedUnion A.P A.R A.one (twoStepNames Q t) (twoStepTailSelector A.P A.R Q t) f.val)⟩ₖ ∈ G) :
    ∀ i ∈ α, (A.ofName f) ‘ i ∈ A.projectionQuotientFilter G := by
  apply mem_of_selected_tail_bound A h hG hA
    ⟨_, forcingLocalCanonicalName_isName _ _ _ _ _ _⟩ hq
    (mem_function_of_mem_function_of_subset hf.1 sep_subset)
  · intro i hi c hc he
    have hcQ := he ▸ function_value_mem hf.1 hi
    have hcG := ((A.check_mem_projectionQuotient_iff (twoStepProjection_maps A.P A.R Q t)).mp hcQ).2
    rwa [twoStepProjection_value hc] at hcG
  · exact (local_collapse_directed_union_bound A h hδ hP hp f hf hκ hκδ hα hDC hQ hS).2

end TwoStepModel

namespace ForcingContext

theorem twoStepQuotient_separative_directedClosedAt (A : ForcingContext V) {Q S t : V}
    (h : IsForcingIterand A.P A.R Q S t) {α : A.Model}
    (hc : IsForcingDirectedClosedAt (A.ofName ⟨Q, h.posetName⟩)
      (forcingSeparativeOrder (A.ofName ⟨Q, h.posetName⟩) (A.ofName ⟨S, h.orderName⟩)) α) :
    IsForcingDirectedClosedAt
      (A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t))
      (forcingSeparativeOrder
        (A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t))
        (A.projectionQuotientOrder (twoStepConditions A.P A.R Q t)
          (twoStepOrder A.P A.R Q S t) (twoStepProjection A.P A.R Q t))) α :=
  (A.twoStepQuotientProjection_projection h).separative_directedClosedAt
    (fun _ ha _ hb ↦ A.twoStepQuotientProjection_compatible_iff h ha hb)
    (fun _ hx ↦ A.twoStepQuotientProjection_surjective h hx) hc

/-- The actual collapse quotient has directed bounds at every ordinal below
its interpreted regular lower index, assuming the corresponding internal DC. -/
theorem twoStepCollapseQuotient_separative_directedClosedAt (A : ForcingContext V)
    {Q S t : V} (h : IsForcingIterand A.P A.R Q S t) {κ δ α : A.Model}
    (hκ : IsRegularCardinal κ) (hα : α ∈ κ) (hDC : InternalDependentChoiceAt α)
    (hQ : A.ofName ⟨Q, h.posetName⟩ = woodinCollapse κ δ)
    (hS : A.ofName ⟨S, h.orderName⟩ = woodinCollapseOrder κ δ) :
    IsForcingDirectedClosedAt
      (A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t))
      (forcingSeparativeOrder
        (A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t))
        (A.projectionQuotientOrder (twoStepConditions A.P A.R Q t)
          (twoStepOrder A.P A.R Q S t) (twoStepProjection A.P A.R Q t))) α := by
  apply A.twoStepQuotient_separative_directedClosedAt h
  rw [hQ, hS]
  exact woodinCollapse_separative_directedClosedAt hκ hα hDC

/-- Restricting to a later quotient preserves directedness when every selected
condition has its intermediate prefix in the later generic. -/
theorem projectionQuotient_directed_tower (A C : ForcingContext V)
    {Q S π τ ρ E : V} {α f : A.Model}
    (hτ : IsForcingSplitProjection A.P A.R C.P C.R τ E)
    (hA : forcingProjectionGeneric A.P A.R τ C.G = A.G)
    (hπ : π ∈ A.P ^ Q) (hρ : IsForcingProjection C.P C.R Q S ρ)
    (hS : IsForcingPreorder Q S) (he : ∀ s ∈ Q, τ ‘ (ρ ‘ s) = π ‘ s)
    (hf : IsForcingDirectedFamily (A.projectionQuotient Q π)
      (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) α f)
    (hfirst : ∀ i ∈ α, ∀ q ∈ Q, f ‘ i = A.check q → ρ ‘ q ∈ C.G) :
    IsForcingDirectedFamily (C.projectionQuotient Q ρ)
      (forcingSeparativeOrder (C.projectionQuotient Q ρ) (C.projectionQuotientOrder Q S ρ))
      (A.projectionInclusion C hτ hA α) (A.projectionInclusion C hτ hA f) := by
  let j := A.projectionInclusion C hτ hA
  have hval (i : A.Model) (hi : i ∈ α) : j (f ‘ i) ∈ C.projectionQuotient Q ρ := by
    obtain ⟨q, hq, _, hqi⟩ := (A.mem_projectionQuotient_iff hπ _).mp (function_value_mem hf.1 hi)
    rw [hqi, A.projectionInclusion_check C hτ hA]
    exact (C.check_mem_projectionQuotient_iff hρ.maps).mpr ⟨hq, hfirst i hi q hq hqi⟩
  have hfj := (j.function_iff f α (A.projectionQuotient Q π)).mpr hf.1
  let := IsFunction.of_mem hfj
  have hle (a b : A.Model) (ha : a ∈ α) (hb : b ∈ α)
      (hab : ⟨f ‘ a, f ‘ b⟩ₖ ∈ forcingSeparativeOrder
        (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) :
      ⟨(j f) ‘ (j a), (j f) ‘ (j b)⟩ₖ ∈ forcingSeparativeOrder
        (C.projectionQuotient Q ρ) (C.projectionQuotientOrder Q S ρ) := by
    obtain ⟨q, hq, _, hqa⟩ := (A.mem_projectionQuotient_iff hπ _).mp (function_value_mem hf.1 ha)
    obtain ⟨r, hr, _, hrb⟩ := (A.mem_projectionQuotient_iff hπ _).mp (function_value_mem hf.1 hb)
    rw [← j.map_value_total, ← j.map_value_total, hqa, hrb]
    change ⟨A.projectionInclusion C hτ hA (A.check q),
      A.projectionInclusion C hτ hA (A.check r)⟩ₖ ∈ _
    rw [A.projectionInclusion_check C hτ hA q, A.projectionInclusion_check C hτ hA r]
    apply A.projectionQuotient_separative_tower C hτ hA hπ hρ hS he
    · exact (C.check_mem_projectionQuotient_iff hρ.maps).mpr ⟨hq, hfirst a ha q hq hqa⟩
    · exact (C.check_mem_projectionQuotient_iff hρ.maps).mpr ⟨hr, hfirst b hb r hr hrb⟩
    · simpa only [hqa, hrb] using hab
  refine ⟨mem_function.intro ?_ (exists_unique_of_mem_function hfj), ?_⟩
  · intro z hz
    obtain ⟨i, hi, y, _, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hfj z hz)
    obtain ⟨a, ha, rfl⟩ := j.endExtension α i hi
    have hy : y = j (f ‘ a) :=
      (value_eq_of_kpair_mem hz).symm.trans (j.map_value_total f a).symm
    exact kpair_mem_iff.mpr ⟨hi, hy ▸ hval a ha⟩
  · intro i hi k hk
    obtain ⟨a, ha, rfl⟩ := j.endExtension α i hi
    obtain ⟨b, hb, rfl⟩ := j.endExtension α k hk
    obtain ⟨c, hc, hca, hcb⟩ := hf.2 a ha b hb
    exact ⟨j c, (j.mem_iff c α).mpr hc, hle c a hc ha hca, hle c b hc hb hcb⟩

theorem transported_twoStep_quotient_directed (A C : ForcingContext V)
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
      (A.ofName f) ‘ i = A.check c → kpair.π₁ c ∈ C.G) :
    IsForcingDirectedFamily
      (C.projectionQuotient (twoStepConditions C.P C.R Q t) (twoStepProjection C.P C.R Q t))
      (forcingSeparativeOrder
        (C.projectionQuotient (twoStepConditions C.P C.R Q t) (twoStepProjection C.P C.R Q t))
        (C.projectionQuotientOrder (twoStepConditions C.P C.R Q t) (twoStepOrder C.P C.R Q S t)
          (twoStepProjection C.P C.R Q t)))
      (A.projectionInclusion C hτ hA α)
      (C.ofName ⟨nameAction E f.val, nameAction_isName hτ.maps f.property⟩) := by
  rw [A.projectionInclusion_nameAction C hτ hA f]
  refine A.projectionQuotient_directed_tower C hτ hA hπ
    (twoStep_projection C.order C.top h) (twoStep_preorder C.order C.top h) ?_ hf ?_
  · intro c hc
    rw [twoStepProjection_value hc]
    exact he c hc
  · intro i hi c hc hci
    rw [twoStepProjection_value hc]
    exact hfirst i hi c hc hci

theorem transported_twoStep_quotient_directed_of_bound (A C : ForcingContext V)
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
        forcingSeparativeOrder (A.projectionQuotient C.P τ) (A.projectionQuotientOrder C.P C.R τ)) :
    IsForcingDirectedFamily
      (C.projectionQuotient (twoStepConditions C.P C.R Q t) (twoStepProjection C.P C.R Q t))
      (forcingSeparativeOrder
        (C.projectionQuotient (twoStepConditions C.P C.R Q t) (twoStepProjection C.P C.R Q t))
        (C.projectionQuotientOrder (twoStepConditions C.P C.R Q t) (twoStepOrder C.P C.R Q S t)
          (twoStepProjection C.P C.R Q t)))
      (A.projectionInclusion C hτ hA α)
      (C.ofName ⟨nameAction E f.val, nameAction_isName hτ.maps f.property⟩) := by
  apply A.transported_twoStep_quotient_directed C hτ hA h hπ he f hf
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

theorem transported_twoStep_tail_directed (A C : ForcingContext V)
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
      (A.ofName f) ‘ i = A.check c → kpair.π₁ c ∈ C.G) :
    IsForcingDirectedFamily (C.ofName ⟨Q, h.posetName⟩)
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
  exact TwoStepModel.selected_tail_directed C h
    (A.transported_twoStep_quotient_directed C hτ hA h hπ he f hf hfirst)

end ForcingContext
end ZFVP
