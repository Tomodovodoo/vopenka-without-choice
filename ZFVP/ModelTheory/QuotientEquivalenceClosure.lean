import ZFVP.ModelTheory.QuotientEquivalenceTransport
import ZFVP.ModelTheory.SplitSeparativeClosureEquivalence
import ZFVP.ModelTheory.ProjectionQuotientClosureTransport
import ZFVP.SetTheory.MembershipIso

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext
variable (A B : ForcingContext V) (e : A.Model ≃ B.Model)
  (hm : ∀ x y, e x ∈ e y ↔ x ∈ y) (hc : ∀ x, e (A.check x) = B.check x)
  {Q S π K L ρ u v : V}
  (hπ : π ∈ A.P ^ Q) (hρ : ρ ∈ B.P ^ K) (hu : u ∈ K ^ Q) (hv : v ∈ Q ^ K)
  (hg : ∀ p ∈ Q, ρ ‘ (u ‘ p) ∈ B.G ↔ π ‘ p ∈ A.G)
  (hi : ∀ q ∈ K, u ‘ (v ‘ q) = q)
  (ho : ∀ p ∈ Q, ∀ q ∈ Q, ⟨u ‘ p, u ‘ q⟩ₖ ∈ L ↔ ⟨p, q⟩ₖ ∈ S)

include hm hc hπ hρ hu hv hg hi ho in
theorem projectionQuotient_equivalence_closedAt_iff (α : A.Model) [IsOrdinal α] :
    IsForcingClosedAt (A.projectionQuotient Q π)
      (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) α ↔
    IsForcingClosedAt (B.projectionQuotient K ρ)
      (forcingSeparativeOrder (B.projectionQuotient K ρ) (B.projectionQuotientOrder K L ρ)) (e α) := by
  have hs := A.transportedProjectionQuotient_splitProjection B e hm hc hπ hρ hu hv hg hi ho
  have hc' := hs.separative_closedAt_iff_of_order_reflecting
    (A.transportedProjectionQuotientMap_order_iff B e hm hc hπ hρ hu hg ho) (α := α)
  have ht := (ElementaryMap.ofMembershipIso e hm).forcingSeparativeClosedAt_iff
    (A.transportedProjectionQuotient B e K ρ)
    (A.transportedProjectionQuotientOrder B e K L ρ) α
  change _ ↔ IsForcingClosedAt (e (e.symm _))
    (forcingSeparativeOrder (e (e.symm _)) (e (e.symm _))) (e α) at ht
  simp only [Equiv.apply_symm_apply] at ht
  exact hc'.trans ht

include hm hc hπ hρ hu hv hg hi ho in
theorem projectionQuotient_equivalence_closedBelow_iff (κ : A.Model) [IsOrdinal κ] :
    IsForcingClosedBelow (A.projectionQuotient Q π)
      (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) κ ↔
    IsForcingClosedBelow (B.projectionQuotient K ρ)
      (forcingSeparativeOrder (B.projectionQuotient K ρ) (B.projectionQuotientOrder K L ρ)) (e κ) := by
  have hs := A.transportedProjectionQuotient_splitProjection B e hm hc hπ hρ hu hv hg hi ho
  have hc' := hs.separative_closedBelow_iff_of_order_reflecting
    (A.transportedProjectionQuotientMap_order_iff B e hm hc hπ hρ hu hg ho) (κ := κ)
  have ht := (ElementaryMap.ofMembershipIso e hm).forcingSeparativeClosedBelow_iff
    (A.transportedProjectionQuotient B e K ρ)
    (A.transportedProjectionQuotientOrder B e K L ρ) κ
  change _ ↔ IsForcingClosedBelow (e (e.symm _))
    (forcingSeparativeOrder (e (e.symm _)) (e (e.symm _))) (e κ) at ht
  simp only [Equiv.apply_symm_apply] at ht
  exact hc'.trans ht

include hm hc hπ hρ hu hv hg hi ho in
theorem projectionQuotient_equivalence_closedBelow_check_iff (κ : V) [IsOrdinal κ] :
    IsForcingClosedBelow (A.projectionQuotient Q π)
      (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) (A.check κ) ↔
    IsForcingClosedBelow (B.projectionQuotient K ρ)
      (forcingSeparativeOrder (B.projectionQuotient K ρ) (B.projectionQuotientOrder K L ρ)) (B.check κ) := by
  simpa only [hc] using
    A.projectionQuotient_equivalence_closedBelow_iff B e hm hc hπ hρ hu hv hg hi ho (A.check κ)

end ForcingContext
end ZFVP
