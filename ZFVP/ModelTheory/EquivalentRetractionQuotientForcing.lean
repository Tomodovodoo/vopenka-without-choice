import ZFVP.ModelTheory.EquivalentRetractionGenericContext
import ZFVP.ModelTheory.QuotientEquivalenceClosure
import ZFVP.ModelTheory.ProjectionQuotientClosureForcing
import ZFVP.ModelTheory.RetractionIsomorphism

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem equivalentRetraction_quotient_closedBelow_forced_countable [Countable V]
    {P R one N T n P' R' f Q S π K L ρ u v κ : V} [IsOrdinal κ]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hr : IsForcingRetraction N T P R n) (hT : IsForcingPreorder N T)
    (hone : one ∈ N) (he : ∀ p ∈ P, ⟨n ‘ p, p⟩ₖ ∈ R)
    (hf : IsForcingIsomorphism N T P' R' f) (hR' : IsForcingPreorder P' R')
    (hπ : IsForcingProjection P R Q S π) (hS : IsForcingPreorder Q S)
    (hρ : IsForcingProjection P' R' K L ρ) (hL : IsForcingPreorder K L)
    (hu : u ∈ K ^ Q) (hv : v ∈ Q ^ K)
    (hi : ∀ q ∈ K, u ‘ (v ‘ q) = q)
    (ho : ∀ p ∈ Q, ∀ q ∈ Q, ⟨u ‘ p, u ‘ q⟩ₖ ∈ L ↔ ⟨p, q⟩ₖ ∈ S)
    (hcomm : ∀ p ∈ Q, ρ ‘ (u ‘ p) = (compose n f) ‘ (π ‘ p))
    (hclosed : ForcesProjectionQuotientClosedBelow P R one Q S π κ) :
    ForcesProjectionQuotientClosedBelow P' R' (f ‘ one) K L ρ κ := by
  have htop' := hf.map_top (hr.top_of_mem htop hone)
  apply projectionQuotient_closedBelow_forced_of_generics hR' htop' hρ hL
  intro H hH
  let G := forcingProjectionPreimage P (compose n f) H
  have hG : IsExternalForcingGeneric P R G := hr.isomorphism_generic_preimage hf hR he hH
  let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  let B := A.retractionIsomorphismImage hr hT hone hf hR'
  let C : ForcingContext V := ⟨P', R', f ‘ one, H, hR', htop', hH⟩
  have hBG : B.G = H := by
    change forcingProjectionGeneric P' R' f (forcingProjectionGeneric N T n G) = H
    rw [forcingProjectionGeneric_comp hf.projection hr.projection hR' hT hG.1]
    exact (hr.isomorphism_projection hf).image_preimage (hr.isomorphism_surjective hf) hR' hH.1
  have hctx : B = C := by
    dsimp [B, C, ForcingContext.retractionIsomorphismImage, ForcingContext.retractionImage,
      ForcingContext.isomorphismImage, A]
    congr 1
  have hg : ∀ p ∈ Q, ρ ‘ (u ‘ p) ∈ B.G ↔ π ‘ p ∈ A.G := by
    intro p hp
    rw [hBG, hcomm p hp]
    change _ ↔ π ‘ p ∈ P ∧ (compose n f) ‘ (π ‘ p) ∈ H
    simp only [function_value_mem hπ.maps hp, true_and]
  have hA := A.projectionQuotient_closedBelow_of_forced hπ hS hclosed
  have hB := (A.projectionQuotient_equivalence_closedBelow_check_iff B
    (A.retractionIsomorphismImageEquiv hr hT hone he hf hR')
    (A.retractionIsomorphismImageEquiv_mem hr hT hone he hf hR')
    (A.retractionIsomorphismImageEquiv_check hr hT hone he hf hR')
    hπ.maps hρ.maps hu hv hg hi ho κ).mp hA
  rw [hctx] at hB
  exact hB

end ZFVP

