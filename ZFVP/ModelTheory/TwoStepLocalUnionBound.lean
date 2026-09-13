import ZFVP.ModelTheory.LocalSelectedUnionBound
import ZFVP.ModelTheory.TwoStepSelectedDescending

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TwoStepModel
variable (A : ForcingContext V) {Q S t : V} (h : IsForcingIterand A.P A.R Q S t)

theorem local_collapse_union_bound {δ p : V}
    (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ) (hp : p ∈ A.G)
    (f : ForcingName A.P) {κ α : A.Model} [IsOrdinal α]
    (hf : IsForcingDescending
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
  have hs := selected_tail_descending A h hf
  rw [hQ, hS] at hs ⊢
  exact A.localSelectedUnion_collapse_bound hδ hP hp (fun _ hτ ↦ h.name hτ)
    (twoStepTailSelector_maps A.P A.R Q t) f
    (mem_function_of_mem_function_of_subset hf.1 sep_subset) hκ hκδ hα hDC hs

theorem mem_of_local_collapse_union {δ p q : V}
    (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ) (hp : p ∈ A.G)
    (f : ForcingName A.P) {κ α : A.Model} [IsOrdinal α]
    (hf : IsForcingDescending
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
  · exact (local_collapse_union_bound A h hδ hP hp f hf hκ hκδ hα hDC hQ hS).2

end TwoStepModel
end ZFVP
