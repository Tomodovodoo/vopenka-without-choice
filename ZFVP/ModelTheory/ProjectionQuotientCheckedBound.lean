import ZFVP.ModelTheory.ProjectionGenericBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ForcingContext.projectionQuotient_checked_bound_mem_generic (A : ForcingContext V)
    {Q S π E t p : V} (hS : IsForcingPreorder Q S)
    (hπ : IsForcingSplitProjection A.P A.R Q S π E)
    {G : Set V} (hG : IsExternalForcingGeneric Q S G)
    (he : forcingProjectionGeneric A.P A.R π G = A.G) (ht : t ∈ G)
    (hb : ⟨A.check t, A.check p⟩ₖ ∈ forcingSeparativeOrder
      (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) : p ∈ G := by
  have hp : A.check p ∈ A.projectionQuotientFilter G :=
    externalForcingGeneric_separative_upward (A.projectionQuotient_preorder hπ.projection.maps hS)
      (A.projectionQuotient_generic hπ hS hG he) ⟨t, ht, rfl⟩ hb
  obtain ⟨q, hq, heq⟩ := hp
  exact ((A.check_eq_iff p q).mp heq) ▸ hq

end ZFVP
