import ZFVP.ModelTheory.EquivalentRetractionQuotientTransfer
import ZFVP.SetTheory.ForcingAutomorphisms

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem identity_retraction (P R : V) :
    IsForcingRetraction P R P R (identity P) := by
  refine ⟨identity_mem_function P, fun _ h ↦ h, fun _ h ↦ identity_value h, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    simpa only [identity_value hp, identity_value hq] using hpq
  · intro q hq p _
    rw [identity_value hq]
  · intro q hq p hp hpq
    exact ⟨p, hp, by simpa only [identity_value hq] using hpq, identity_value hp⟩

theorem sameBase_quotient_closedBelow_forced
    {P R one Q S π K L ρ u v κ : V} [IsOrdinal κ]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hπ : IsForcingProjection P R Q S π) (hS : IsForcingPreorder Q S)
    (hρ : IsForcingProjection P R K L ρ) (hL : IsForcingPreorder K L)
    (hu : u ∈ K ^ Q) (hv : v ∈ Q ^ K)
    (hi : ∀ q ∈ K, u ‘ (v ‘ q) = q)
    (ho : ∀ p ∈ Q, ∀ q ∈ Q, ⟨u ‘ p, u ‘ q⟩ₖ ∈ L ↔ ⟨p, q⟩ₖ ∈ S)
    (hcomm : ∀ p ∈ Q, ρ ‘ (u ‘ p) = π ‘ p)
    (hclosed : ForcesProjectionQuotientClosedBelow P R one Q S π κ) :
    ForcesProjectionQuotientClosedBelow P R one K L ρ κ := by
  have hf : IsForcingIsomorphism P R P R (identity P) := forcingAutomorphism_identity P R
  have he : ∀ p ∈ P, ⟨(identity P) ‘ p, p⟩ₖ ∈ R := by
    intro p hp
    rw [identity_value hp]
    exact hR.2.1 p hp
  have ht := equivalentRetraction_quotient_closedBelow_forced hR htop
    (identity_retraction P R) hR htop.1 he hf hR hπ hS hρ hL hu hv hi ho (fun p hp ↦ ?_) hclosed
  · simpa only [identity_value htop.1] using ht
  rw [value_compose_of_mem_function (identity_mem_function P) (identity_mem_function P)
    (function_value_mem hπ.maps hp), identity_value (function_value_mem hπ.maps hp),
    identity_value (function_value_mem hπ.maps hp)]
  exact hcomm p hp

end ZFVP
