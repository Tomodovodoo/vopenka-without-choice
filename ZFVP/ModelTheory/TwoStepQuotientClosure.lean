import ZFVP.ModelTheory.TwoStepQuotientProjection
import ZFVP.ModelTheory.ProjectionSeparativeClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext

theorem twoStepQuotientProjection_surjective (A : ForcingContext V) {Q S t : V}
    (h : IsForcingIterand A.P A.R Q S t) {x : A.Model}
    (hx : x ∈ A.ofName ⟨Q, h.posetName⟩) :
    ∃ a ∈ A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t),
      (A.twoStepQuotientProjection h) ‘ a = x := by
  obtain ⟨σ, p, hp, hσp, rfl⟩ := (A.mem_ofName_iff ⟨Q, h.posetName⟩ x).mp hx
  have hc : ⟨p, σ.val⟩ₖ ∈ twoStepConditions A.P A.R Q t :=
    (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr
      ⟨A.generic.1.1 p hp, mem_union_iff.mpr (Or.inl (mem_domain_of_kpair_mem hσp)),
        atomicMembership_of_pair A.order (A.generic.1.1 p hp) hσp⟩
  have hcq := (A.check_mem_projectionQuotient_iff (twoStepProjection_maps A.P A.R Q t)).mpr
    ⟨hc, by simpa only [twoStepProjection_value hc, kpair.π₁_kpair] using hp⟩
  exact ⟨_, hcq, A.twoStepQuotientProjection_value h σ hc hp⟩

/-- Closure in the separative order of the interpreted iterand yields closure
in the separative order of the two-step quotient, for all intermediate sequences. -/
theorem twoStepQuotient_separative_closedAt (A : ForcingContext V) {Q S t : V}
    (h : IsForcingIterand A.P A.R Q S t) {α : A.Model} [IsOrdinal α]
    (hc : IsForcingClosedAt (A.ofName ⟨Q, h.posetName⟩)
      (forcingSeparativeOrder (A.ofName ⟨Q, h.posetName⟩) (A.ofName ⟨S, h.orderName⟩)) α) :
    IsForcingClosedAt
      (A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t))
      (forcingSeparativeOrder
        (A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t))
        (A.projectionQuotientOrder (twoStepConditions A.P A.R Q t)
          (twoStepOrder A.P A.R Q S t) (twoStepProjection A.P A.R Q t))) α :=
  (A.twoStepQuotientProjection_projection h).separative_closedAt
    (fun _ ha _ hb ↦ A.twoStepQuotientProjection_compatible_iff h ha hb)
    (fun _ hx ↦ A.twoStepQuotientProjection_surjective h hx) hc

end ForcingContext
end ZFVP
