import ZFVP.ModelTheory.SeparativeGeneric
import ZFVP.ModelTheory.ProjectionQuotientReconstruction
import ZFVP.ModelTheory.ProjectionQuotientGeneric

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingSeparativeOrder_of_all_generics [Countable V] {P R p q : V}
    (hR : IsForcingPreorder P R) (hp : p ∈ P) (hq : q ∈ P)
    (h : ∀ (G : Set V), IsExternalForcingGeneric P R G → p ∈ G → q ∈ G) :
    ⟨p, q⟩ₖ ∈ forcingSeparativeOrder P R := by
  apply (kpair_mem_forcingSeparativeOrder _ _ _ _).mpr
  refine ⟨hp, hq, ?_⟩
  intro r hr hrp
  obtain ⟨G, hG, hrG⟩ := exists_externalForcingGeneric hR hr
  have hpG := hG.1.2.2.1 r hrG p hp hrp
  obtain ⟨s, hsG, hsr, hsq⟩ := hG.1.2.2.2 r hrG q (h G hG hpG)
  exact ⟨s, hG.1.1 s hsG, hsr, hsq⟩

namespace ForcingContext
variable (A : ForcingContext V)

theorem projectionQuotient_separative_of_all_generics [Countable A.Model]
    {Q S π q : V} {x : A.Model}
    (hπ : IsForcingProjection A.P A.R Q S π) (hS : IsForcingPreorder Q S)
    (hq : A.check q ∈ A.projectionQuotient Q π) (hx : x ∈ A.projectionQuotient Q π)
    (h : ∀ (G : Set V), IsExternalForcingGeneric Q S G →
      forcingProjectionGeneric A.P A.R π G = A.G → q ∈ G →
        x ∈ A.projectionQuotientFilter G) :
    ⟨A.check q, x⟩ₖ ∈ forcingSeparativeOrder (A.projectionQuotient Q π)
      (A.projectionQuotientOrder Q S π) := by
  apply forcingSeparativeOrder_of_all_generics (A.projectionQuotient_preorder hπ.maps hS) hq hx
  intro H hH hqH
  have hqQ := ((A.check_mem_projectionQuotient_iff hπ.maps).mp hq).1
  have hxH := h (A.projectionCombinedFilter Q H) (A.projectionCombined_generic hπ hS hH)
    (A.projectionCombined_projection hπ hH) ⟨hqQ, hqH⟩
  rwa [A.projectionCombined_quotientFilter hπ.maps hH.1] at hxH

theorem projectionQuotient_separative_generic_iff [Countable A.Model]
    {Q S π E q : V} {x : A.Model}
    (hπ : IsForcingSplitProjection A.P A.R Q S π E) (hS : IsForcingPreorder Q S)
    (hq : A.check q ∈ A.projectionQuotient Q π) (hx : x ∈ A.projectionQuotient Q π) :
    ⟨A.check q, x⟩ₖ ∈ forcingSeparativeOrder (A.projectionQuotient Q π)
      (A.projectionQuotientOrder Q S π) ↔
    ∀ (G : Set V), IsExternalForcingGeneric Q S G →
      forcingProjectionGeneric A.P A.R π G = A.G → q ∈ G →
        x ∈ A.projectionQuotientFilter G := by
  constructor
  · intro h G hG he hqG
    exact externalForcingGeneric_separative_upward (A.projectionQuotient_preorder hπ.projection.maps hS)
      (A.projectionQuotient_generic hπ hS hG he) ⟨q, hqG, rfl⟩ h
  · exact A.projectionQuotient_separative_of_all_generics hπ.projection hS hq hx

end ForcingContext
end ZFVP
