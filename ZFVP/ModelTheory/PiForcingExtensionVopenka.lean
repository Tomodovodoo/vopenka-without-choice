import ZFVP.ModelTheory.PiSymmetricVopenkaPreservation
import ZFVP.ModelTheory.ForcingExtensionVopenka
import ZFVP.ModelTheory.SymmetricExtensionVopenka

/-! Positive Pi fragments of VP in ordinary quotients and evaluated forcing extensions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ForcingContext.pi_vopenka_preservation (S : ForcingContext V) (hP : IsForcingPoset S.P S.R)
    {k : ℕ} (hk : 0 < k)
    (hVP : ∀ ψ : SetTheorySemisentence 2, IsPiFormula k ψ → VopenkaInstance (V := V) ψ) :
    ∀ φ : SetTheorySemisentence 2, IsPiFormula k φ → VopenkaInstance (V := S.Model) φ := by
  intro φ hφ
  exact @vopenkaInstance_of_membershipIso (S.trivialSymmetricContext hP).Model S.Model
    (SymmetricContext.modelSetStructure _) (ForcingContext.modelSetStructure S)
    (SymmetricContext.modelNonempty _) (ForcingContext.modelNonempty S)
    (SymmetricContext.modelZF _) (ForcingContext.modelZF S) (S.trivialSymmetricEquiv hP)
    (S.trivialSymmetricContext hP).toOrdinary_mem_iff φ
    ((S.trivialSymmetricContext hP).pi_vopenka_preservation hk hVP φ hφ)

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem symmetricExtensionDomain_pi_vopenka (P R Γ F one : SetDomain U) (G : V)
    (hR : IsForcingPoset P R) (hΓ : IsForcingAutomorphismGroup P R Γ)
    (hF : IsNormalSubgroupFilter P Γ F) (hone : IsForcingTop P R one)
    (hG : IsGroundForcingGeneric U P.val R.val G) {k : ℕ} (hk : 0 < k)
    (hVP : ∀ ψ : SetTheorySemisentence 2, IsPiFormula k ψ → VopenkaInstance (V := SetDomain U) ψ) :
    let _ := symmetricExtensionDomain_nonempty U P R Γ F one G hR hΓ hF hone hG
    let _ := symmetricExtensionDomain_models_zf U P R Γ F one G hR hΓ hF hone hG
    ∀ φ : SetTheorySemisentence 2, IsPiFormula k φ →
      VopenkaInstance (V := SetDomain (symmetricExtensionDomain U P.val Γ.val F.val G)) φ := by
  let S := groundSymmetricContext U P R Γ F one G hR hΓ hF hone hG
  let := symmetricExtensionDomain_nonempty U P R Γ F one G hR hΓ hF hone hG
  let := symmetricExtensionDomain_models_zf U P R Γ F one G hR hΓ hF hone hG
  let e : S.Model ≃ SetDomain (symmetricExtensionDomain U P.val Γ.val F.val G) :=
    symmetricQuotientEquiv U P R Γ F G hR.1 hG
  dsimp only
  intro φ hφ
  exact @vopenkaInstance_of_membershipIso S.Model _ (SymmetricContext.modelSetStructure S) inferInstance
    (SymmetricContext.modelNonempty S) inferInstance (SymmetricContext.modelZF S) inferInstance e
    (symmetricQuotientEquiv_mem_iff U P R Γ F G hR.1 hG) φ (S.pi_vopenka_preservation hk hVP φ hφ)

theorem forcingExtensionDomain_pi_vopenka (P R one : SetDomain U) (G : V)
    (hR : IsForcingPoset P R) (hone : IsForcingTop P R one)
    (hG : IsGroundForcingGeneric U P.val R.val G) {k : ℕ} (hk : 0 < k)
    (hVP : ∀ ψ : SetTheorySemisentence 2, IsPiFormula k ψ → VopenkaInstance (V := SetDomain U) ψ) :
    let _ := forcingExtensionDomain_models_zf U P R one G ((forcingPreorder_iff U P R).mp hR.1)
      ((forcingTop_iff U P R one).mp hone) hG
    ∀ φ : SetTheorySemisentence 2, IsPiFormula k φ →
      VopenkaInstance (V := SetDomain (forcingExtensionDomain U P.val G)) φ := by
  let S : ForcingContext (SetDomain U) := {
    P := P, R := R, one := one, G := {p : SetDomain U | p.val ∈ G}, order := hR.1, top := hone,
    generic := (groundForcingGeneric_iff_external U P R G hG.1.1).mp hG }
  let := forcingExtensionDomain_models_zf U P R one G ((forcingPreorder_iff U P R).mp hR.1)
    ((forcingTop_iff U P R one).mp hone) hG
  let e : S.Model ≃ SetDomain (forcingExtensionDomain U P.val G) := forcingQuotientEquiv U P R G hR.1 hG
  dsimp only
  intro φ hφ
  exact @vopenkaInstance_of_membershipIso S.Model _ (ForcingContext.modelSetStructure S) inferInstance
    (ForcingContext.modelNonempty S) inferInstance (ForcingContext.modelZF S) inferInstance e
    (forcingQuotientEquiv_mem_iff U P R G hR.1 hG) φ (S.pi_vopenka_preservation hR hk hVP φ hφ)

end TransitiveZF

end ZFVP
