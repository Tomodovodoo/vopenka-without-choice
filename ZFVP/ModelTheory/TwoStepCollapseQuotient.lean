import ZFVP.ModelTheory.TwoStepQuotientClosure
import ZFVP.SetTheory.WoodinCollapseSeparative

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext

/-- Any set presentation of a Woodin collapse gives a separatively closed
two-step quotient, with dependent choice assumed only at the sequence length. -/
theorem twoStep_collapse_quotient_closedAt (A : ForcingContext V) {Q S t : V}
    (h : IsForcingIterand A.P A.R Q S t) {κ δ α : A.Model}
    (hQ : A.ofName ⟨Q, h.posetName⟩ = woodinCollapse κ δ)
    (hS : A.ofName ⟨S, h.orderName⟩ = woodinCollapseOrder κ δ)
    (hκ : IsRegularCardinal κ) (hα : α ∈ κ) (hDC : InternalDependentChoiceAt α) :
    IsForcingClosedAt
      (A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t))
      (forcingSeparativeOrder
        (A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t))
        (A.projectionQuotientOrder (twoStepConditions A.P A.R Q t)
          (twoStepOrder A.P A.R Q S t) (twoStepProjection A.P A.R Q t))) α := by
  let := hκ.1.1
  let := IsOrdinal.of_mem hα
  apply A.twoStepQuotient_separative_closedAt h
  rw [hQ, hS]
  exact woodinCollapse_separative_closedAt hκ hα hDC

end ForcingContext
end ZFVP
