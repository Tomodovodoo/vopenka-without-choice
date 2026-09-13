import ZFVP.ModelTheory.QuotientSplitProjection
import ZFVP.ModelTheory.SplitSeparativeClosureEquivalence

/-! Order-reflecting ground projections induce separative and closure equivalences on quotients. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem projectionQuotientMap_order_iff (A : ForcingContext V) {Q S T U π τ ρ : V}
    (hπ : π ∈ A.P ^ Q) (hτ : τ ∈ A.P ^ T) (hρ : ρ ∈ T ^ Q)
    (he : ∀ q ∈ Q, τ ‘ (ρ ‘ q) = π ‘ q)
    (ho : ∀ q ∈ Q, ∀ r ∈ Q, ⟨ρ ‘ q, ρ ‘ r⟩ₖ ∈ U ↔ ⟨q, r⟩ₖ ∈ S)
    {x y : A.Model} (hx : x ∈ A.projectionQuotient Q π) (hy : y ∈ A.projectionQuotient Q π) :
    ⟨(A.projectionQuotientMap Q π ρ) ‘ x, (A.projectionQuotientMap Q π ρ) ‘ y⟩ₖ ∈
        A.projectionQuotientOrder T U τ ↔ ⟨x, y⟩ₖ ∈ A.projectionQuotientOrder Q S π := by
  have hm := A.projectionQuotientMap_maps hπ hτ hρ he
  have hx' := function_value_mem hm hx
  have hy' := function_value_mem hm hy
  obtain ⟨q, hq, _, rfl⟩ := (A.mem_projectionQuotient_iff hπ x).mp hx
  obtain ⟨r, hr, _, rfl⟩ := (A.mem_projectionQuotient_iff hπ y).mp hy
  rw [A.projectionQuotientMap_value hρ hq hx] at hx' ⊢
  rw [A.projectionQuotientMap_value hρ hr hy] at hy' ⊢
  rw [A.projectionQuotientOrder_pair_iff, A.projectionQuotientOrder_pair_iff]
  simp only [hx, hy, hx', hy', and_true, ← A.check_kpair, A.check_mem_iff]
  exact ho q hq r hr

theorem projectionQuotient_separative_iff_of_order_reflecting (A : ForcingContext V)
    {Q S T U π τ ρ E : V} (hπ : π ∈ A.P ^ Q) (hτ : τ ∈ A.P ^ T)
    (h : IsForcingSplitProjection T U Q S ρ E)
    (he : ∀ q ∈ Q, τ ‘ (ρ ‘ q) = π ‘ q)
    (ho : ∀ q ∈ Q, ∀ r ∈ Q, ⟨ρ ‘ q, ρ ‘ r⟩ₖ ∈ U ↔ ⟨q, r⟩ₖ ∈ S)
    {x y : A.Model} (hx : x ∈ A.projectionQuotient Q π) (hy : y ∈ A.projectionQuotient Q π) :
    ⟨x, y⟩ₖ ∈ forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π) ↔
      ⟨(A.projectionQuotientMap Q π ρ) ‘ x, (A.projectionQuotientMap Q π ρ) ‘ y⟩ₖ ∈
        forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ) :=
  (A.projectionQuotient_splitProjection hπ hτ h he).separative_iff_of_order_reflecting
    (fun _ hx _ hy ↦ A.projectionQuotientMap_order_iff hπ hτ h.projection.maps he ho hx hy) hx hy

theorem projectionQuotient_checked_separative_iff_of_order_reflecting (A : ForcingContext V)
    {Q S T U π τ ρ E q r : V} (hπ : π ∈ A.P ^ Q) (hτ : τ ∈ A.P ^ T)
    (h : IsForcingSplitProjection T U Q S ρ E)
    (he : ∀ q ∈ Q, τ ‘ (ρ ‘ q) = π ‘ q)
    (ho : ∀ q ∈ Q, ∀ r ∈ Q, ⟨ρ ‘ q, ρ ‘ r⟩ₖ ∈ U ↔ ⟨q, r⟩ₖ ∈ S)
    (hq : q ∈ Q) (hr : r ∈ Q)
    (hqG : A.check q ∈ A.projectionQuotient Q π) (hrG : A.check r ∈ A.projectionQuotient Q π) :
    ⟨A.check q, A.check r⟩ₖ ∈
        forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π) ↔
      ⟨A.check (ρ ‘ q), A.check (ρ ‘ r)⟩ₖ ∈
        forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ) := by
  simpa only [A.projectionQuotientMap_value h.projection.maps hq hqG,
    A.projectionQuotientMap_value h.projection.maps hr hrG] using
    A.projectionQuotient_separative_iff_of_order_reflecting hπ hτ h he ho hqG hrG

theorem projectionQuotient_separative_closedAt_iff_of_order_reflecting (A : ForcingContext V)
    {Q S T U π τ ρ E : V} (hπ : π ∈ A.P ^ Q) (hτ : τ ∈ A.P ^ T)
    (h : IsForcingSplitProjection T U Q S ρ E)
    (he : ∀ q ∈ Q, τ ‘ (ρ ‘ q) = π ‘ q)
    (ho : ∀ q ∈ Q, ∀ r ∈ Q, ⟨ρ ‘ q, ρ ‘ r⟩ₖ ∈ U ↔ ⟨q, r⟩ₖ ∈ S)
    {α : A.Model} [IsOrdinal α] :
    IsForcingClosedAt (A.projectionQuotient Q π)
        (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) α ↔
      IsForcingClosedAt (A.projectionQuotient T τ)
        (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) α :=
  (A.projectionQuotient_splitProjection hπ hτ h he).separative_closedAt_iff_of_order_reflecting
    (fun _ hx _ hy ↦ A.projectionQuotientMap_order_iff hπ hτ h.projection.maps he ho hx hy)

theorem projectionQuotient_separative_closedBelow_iff_of_order_reflecting (A : ForcingContext V)
    {Q S T U π τ ρ E : V} (hπ : π ∈ A.P ^ Q) (hτ : τ ∈ A.P ^ T)
    (h : IsForcingSplitProjection T U Q S ρ E)
    (he : ∀ q ∈ Q, τ ‘ (ρ ‘ q) = π ‘ q)
    (ho : ∀ q ∈ Q, ∀ r ∈ Q, ⟨ρ ‘ q, ρ ‘ r⟩ₖ ∈ U ↔ ⟨q, r⟩ₖ ∈ S)
    {κ : A.Model} [IsOrdinal κ] :
    IsForcingClosedBelow (A.projectionQuotient Q π)
        (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) κ ↔
      IsForcingClosedBelow (A.projectionQuotient T τ)
        (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) κ :=
  (A.projectionQuotient_splitProjection hπ hτ h he).separative_closedBelow_iff_of_order_reflecting
    (fun _ hx _ hy ↦ A.projectionQuotientMap_order_iff hπ hτ h.projection.maps he ho hx hy)

end ForcingContext
end ZFVP
