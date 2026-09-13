import ZFVP.ModelTheory.QuotientSplitProjection
import ZFVP.ModelTheory.SplitSeparativeOrder
import ZFVP.SetTheory.ForcingClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ForcingContext.projectionQuotient_section_separative_iff
    (A : ForcingContext V) {Q R T U π τ ρ E q r : V}
    (hπ : π ∈ A.P ^ T) (hτ : τ ∈ A.P ^ Q)
    (h : IsForcingSplitProjection Q R T U ρ E)
    (he : ∀ t ∈ T, τ ‘ (ρ ‘ t) = π ‘ t)
    (hq : q ∈ Q) (hr : r ∈ Q)
    (hqG : A.check q ∈ A.projectionQuotient Q τ)
    (hrG : A.check r ∈ A.projectionQuotient Q τ) :
    ⟨A.check (E ‘ q), A.check (E ‘ r)⟩ₖ ∈
        forcingSeparativeOrder (A.projectionQuotient T π) (A.projectionQuotientOrder T U π) ↔
      ⟨A.check q, A.check r⟩ₖ ∈
        forcingSeparativeOrder (A.projectionQuotient Q τ) (A.projectionQuotientOrder Q R τ) := by
  have hs := A.projectionQuotient_splitProjection hπ hτ h he
  have hh := hs.separative_below (function_value_mem hs.maps hqG) hrG
  rw [hs.right_inverse _ hqG,
    A.projectionQuotientMap_value h.maps hq hqG,
    A.projectionQuotientMap_value h.maps hr hrG] at hh
  exact hh

/-- Closure depends only on the order comparisons between members of its carrier. -/
theorem forcingClosedAt_of_order_agreement {B R S α : V} [IsOrdinal α]
    (hagree : ∀ x ∈ B, ∀ y ∈ B, ⟨x, y⟩ₖ ∈ R ↔ ⟨x, y⟩ₖ ∈ S)
    (hclosed : IsForcingClosedAt B S α) : IsForcingClosedAt B R α := by
  intro f hf
  have hs : IsForcingDescending B S α f := by
    refine ⟨hf.1, fun i hi j hj ↦ ?_⟩
    exact (hagree _ (function_value_mem hf.1 hi) _
      (function_value_mem hf.1 (IsOrdinal.toIsTransitive.mem_trans hj hi))).mp (hf.2 i hi j hj)
  obtain ⟨p, hp, hb⟩ := hclosed f hs
  exact ⟨p, hp, fun i hi ↦ (hagree p hp _ (function_value_mem hf.1 hi)).mpr (hb i hi)⟩

end ZFVP
