import ZFVP.SetTheory.ForcingIterationSystem
import ZFVP.ModelTheory.ForcingSplitProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingIterationSystem.projection {θ P R π E L t i j : V}
    (h : IsForcingIterationSystem θ P R π E L t)
    (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j) :
    IsForcingProjection (P ‘ i) (R ‘ i) (P ‘ j) (R ‘ j) (π ‘ ⟨i, j⟩ₖ) := by
  refine ⟨h.functions.projection i hi j hj hij, h.order.projMono i hi j hj hij, ?_⟩
  intro a ha b hb hba
  exact ⟨(L ‘ ⟨i, j⟩ₖ) ‘ ⟨a, b⟩ₖ, h.lifts.lift i hi j hj hij a ha b hb hba⟩

theorem IsForcingIterationSystem.splitProjection {θ P R π E L t i j : V}
    (h : IsForcingIterationSystem θ P R π E L t)
    (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j) :
    IsForcingSplitProjection (P ‘ i) (R ‘ i) (P ‘ j) (R ‘ j)
      (π ‘ ⟨i, j⟩ₖ) (E ‘ ⟨i, j⟩ₖ) :=
  ⟨h.projection hi hj hij, h.functions.sectionMap i hi j hj hij,
    h.split.retraction i hi j hj hij, h.order.below i hi j hj hij⟩

end ZFVP
