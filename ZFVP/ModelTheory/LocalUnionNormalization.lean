import ZFVP.ModelTheory.TwoStepLocalUnionBound

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TwoStepModel

theorem local_collapse_union_normalization (A : ForcingContext V)
    {Q S t δ p : V} (h : IsForcingIterand A.P A.R Q S t)
    (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ) (hp : p ∈ A.G)
    (f : ForcingName A.P) {κ α : A.Model} [IsOrdinal α]
    (hf : IsForcingDescending
      (A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t))
      (forcingSeparativeOrder
        (A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t))
        (A.projectionQuotientOrder (twoStepConditions A.P A.R Q t)
          (twoStepOrder A.P A.R Q S t) (twoStepProjection A.P A.R Q t))) α (A.ofName f))
    (hκ : IsRegularCardinal κ) (hκδ : κ ⊆ A.check δ) (hα : α ∈ κ)
    (hDC : InternalDependentChoiceAt α)
    (hQ : A.ofName ⟨Q, h.posetName⟩ = woodinCollapse κ (A.check δ))
    (hS : A.ofName ⟨S, h.orderName⟩ = woodinCollapseOrder κ (A.check δ)) :
    let τ := forcingSelectedUnion A.P A.R A.one (twoStepNames Q t) (twoStepTailSelector A.P A.R Q t) f.val
    A.ofName ⟨forcingLocalCanonicalName A.P A.R A.one δ p τ, forcingLocalCanonicalName_isName _ _ _ _ _ _⟩ =
      A.ofName ⟨τ, forcingSelectedUnion_isName _ _ _ _ _ _⟩ := by
  have hs := selected_tail_descending A h hf
  rw [hQ, hS] at hs
  have hu := A.forcingSelectedUnion_collapse_bound (fun _ hν ↦ h.name hν)
    (twoStepTailSelector_maps A.P A.R Q t) f
    (mem_function_of_mem_function_of_subset hf.1 sep_subset) hκ hα hDC hs
  have hr := woodinCollapse_condition_mem_hierarchy
    (A.check_inaccessible_of_small hδ hP).regular hκδ hu.1
  exact A.localCanonicalName_value hδ hP hp
    ⟨_, forcingSelectedUnion_isName _ _ _ _ _ _⟩ hr

end TwoStepModel
end ZFVP
