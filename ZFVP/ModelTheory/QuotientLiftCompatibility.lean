import ZFVP.ModelTheory.ProjectionQuotientSeparative

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext
variable (A : ForcingContext V)

/-- One condition in the base generic suffices for the common-extension test.
The lift is fixed ground data, so no coordinatewise choices are required. -/
theorem projectionQuotient_separative_of_lift {Q S π L q c d : V}
    (hπ : π ∈ A.P ^ Q)
    (hL : ∀ r ∈ Q, ∀ b ∈ A.P, ⟨b, π ‘ r⟩ₖ ∈ A.R →
      L ‘ ⟨r, b⟩ₖ ∈ Q ∧ ⟨L ‘ ⟨r, b⟩ₖ, r⟩ₖ ∈ S ∧ π ‘ (L ‘ ⟨r, b⟩ₖ) = b)
    (hq : A.check q ∈ A.projectionQuotient Q π)
    (hc : A.check c ∈ A.projectionQuotient Q π) (hd : d ∈ A.G)
    (hbelow : ∀ r ∈ Q, ⟨r, q⟩ₖ ∈ S → ∀ b ∈ A.P,
      ⟨b, π ‘ r⟩ₖ ∈ A.R → ⟨b, d⟩ₖ ∈ A.R → ⟨L ‘ ⟨r, b⟩ₖ, c⟩ₖ ∈ S) :
    ⟨A.check q, A.check c⟩ₖ ∈ forcingSeparativeOrder (A.projectionQuotient Q π)
      (A.projectionQuotientOrder Q S π) := by
  refine (kpair_mem_forcingSeparativeOrder _ _ _ _).mpr ⟨hq, hc, ?_⟩
  intro x hx hxq
  obtain ⟨r, hr, hrG, rfl⟩ := (A.mem_projectionQuotient_iff hπ x).mp hx
  have hrq := ((A.projectionQuotientOrder_pair_iff Q S π _ _).mp hxq).1
  rw [← A.check_kpair, A.check_mem_iff] at hrq
  obtain ⟨b, hbG, hbr, hbd⟩ := A.generic.1.2.2.2 _ hrG d hd
  have hb := A.generic.1.1 b hbG
  have hl := hL r hr b hb hbr
  have hlQ := (A.check_mem_projectionQuotient_iff hπ).mpr ⟨hl.1, hl.2.2.symm ▸ hbG⟩
  refine ⟨A.check (L ‘ ⟨r, b⟩ₖ), hlQ, ?_, ?_⟩
  · exact (A.projectionQuotientOrder_pair_iff Q S π _ _).mpr
      ⟨A.check_kpair _ r ▸ (A.check_mem_iff _ _).mpr hl.2.1, hlQ, hx⟩
  · exact (A.projectionQuotientOrder_pair_iff Q S π _ _).mpr
      ⟨A.check_kpair _ c ▸ (A.check_mem_iff _ _).mpr (hbelow r hr hrq b hb hbr hbd), hlQ, hc⟩

end ForcingContext
end ZFVP
