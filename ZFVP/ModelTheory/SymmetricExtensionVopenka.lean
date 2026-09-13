import ZFVP.ModelTheory.SymmetricExtensionZF
import ZFVP.ModelTheory.SymmetricVopenkaPreservation
import ZFVP.SetTheory.VopenkaIsomorphism

/-! Vopenka preservation for the evaluated symmetric extension of a transitive ZF set model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem symmetricExtensionDomain_vopenka (P R Γ F one : SetDomain U) (G : V)
    (hR : IsForcingPoset P R) (hΓ : IsForcingAutomorphismGroup P R Γ)
    (hF : IsNormalSubgroupFilter P Γ F) (hone : IsForcingTop P R one)
    (hG : IsGroundForcingGeneric U P.val R.val G)
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := SetDomain U) ψ) :
    let _ := symmetricExtensionDomain_nonempty U P R Γ F one G hR hΓ hF hone hG
    let _ := symmetricExtensionDomain_models_zf U P R Γ F one G hR hΓ hF hone hG
    ∀ φ : SetTheorySemisentence 2,
      VopenkaInstance (V := SetDomain (symmetricExtensionDomain U P.val Γ.val F.val G)) φ := by
  let S := groundSymmetricContext U P R Γ F one G hR hΓ hF hone hG
  let := symmetricExtensionDomain_nonempty U P R Γ F one G hR hΓ hF hone hG
  let := symmetricExtensionDomain_models_zf U P R Γ F one G hR hΓ hF hone hG
  let e : S.Model ≃ SetDomain (symmetricExtensionDomain U P.val Γ.val F.val G) :=
    symmetricQuotientEquiv U P R Γ F G hR.1 hG
  dsimp only
  intro φ
  exact @vopenkaInstance_of_membershipIso S.Model _ (SymmetricContext.modelSetStructure S) inferInstance
    (SymmetricContext.modelNonempty S) inferInstance (SymmetricContext.modelZF S) inferInstance e
    (symmetricQuotientEquiv_mem_iff U P R Γ F G hR.1 hG) φ (S.vopenkaInstance hVP φ)

end TransitiveZF
end ZFVP
