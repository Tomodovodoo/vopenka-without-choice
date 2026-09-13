import ZFVP.ModelTheory.ForcingExtensionZF
import ZFVP.ModelTheory.ForcingVopenkaPreservation
import ZFVP.ModelTheory.SymmetricExtensionZF

/-! Full Vopenka preservation for an evaluated ordinary forcing extension. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingExtensionDomain_vopenka (P R one : SetDomain U) (G : V)
    (hR : IsForcingPoset P R) (hone : IsForcingTop P R one)
    (hG : IsGroundForcingGeneric U P.val R.val G)
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := SetDomain U) ψ) :
    let _ := forcingExtensionDomain_models_zf U P R one G ((forcingPreorder_iff U P R).mp hR.1)
      ((forcingTop_iff U P R one).mp hone) hG
    ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := SetDomain (forcingExtensionDomain U P.val G)) φ := by
  let S : ForcingContext (SetDomain U) := {
    P := P, R := R, one := one, G := {p : SetDomain U | p.val ∈ G}, order := hR.1, top := hone,
    generic := (groundForcingGeneric_iff_external U P R G hG.1.1).mp hG }
  let := forcingExtensionDomain_models_zf U P R one G ((forcingPreorder_iff U P R).mp hR.1)
    ((forcingTop_iff U P R one).mp hone) hG
  let e : S.Model ≃ SetDomain (forcingExtensionDomain U P.val G) := forcingQuotientEquiv U P R G hR.1 hG
  dsimp only
  intro φ
  exact @vopenkaInstance_of_membershipIso S.Model _ (ForcingContext.modelSetStructure S) inferInstance
    (ForcingContext.modelNonempty S) inferInstance (ForcingContext.modelZF S) inferInstance e
    (forcingQuotientEquiv_mem_iff U P R G hR.1 hG) φ (S.vopenkaInstance hR hVP φ)

end TransitiveZF
end ZFVP
