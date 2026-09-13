import ZFVP.ModelTheory.SymmetricQuotientValuation
import ZFVP.ModelTheory.SymmetricModelZF

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def groundSymmetricContext (P R Γ F one : SetDomain U) (G : V)
    (hR : IsForcingPoset P R) (hΓ : IsForcingAutomorphismGroup P R Γ)
    (hF : IsNormalSubgroupFilter P Γ F) (hone : IsForcingTop P R one)
    (hG : IsGroundForcingGeneric U P.val R.val G) : SymmetricContext (SetDomain U) where
  P := P
  R := R
  one := one
  G := {p : SetDomain U | p.val ∈ G}
  order := hR.1
  top := hone
  generic := (groundForcingGeneric_iff_external U P R G hG.1.1).mp hG
  Γ := Γ
  F := F
  poset := hR
  group := hΓ
  normal := hF

theorem symmetricExtensionDomain_nonempty (P R Γ F one : SetDomain U) (G : V)
    (hR : IsForcingPoset P R) (hΓ : IsForcingAutomorphismGroup P R Γ)
    (hF : IsNormalSubgroupFilter P Γ F) (hone : IsForcingTop P R one)
    (hG : IsGroundForcingGeneric U P.val R.val G) :
    Nonempty (SetDomain (symmetricExtensionDomain U P.val Γ.val F.val G)) :=
  ⟨symmetricQuotientValue U P R Γ F G hR.1 hG
    ((groundSymmetricContext U P R Γ F one G hR hΓ hF hone hG).check ∅)⟩

theorem symmetricExtensionDomain_models_zf (P R Γ F one : SetDomain U) (G : V)
    (hR : IsForcingPoset P R) (hΓ : IsForcingAutomorphismGroup P R Γ)
    (hF : IsNormalSubgroupFilter P Γ F) (hone : IsForcingTop P R one)
    (hG : IsGroundForcingGeneric U P.val R.val G) :
    let _ := symmetricExtensionDomain_nonempty U P R Γ F one G hR hΓ hF hone hG
    (SetDomain (symmetricExtensionDomain U P.val Γ.val F.val G))↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  let S := groundSymmetricContext U P R Γ F one G hR hΓ hF hone hG
  let e : S.Model ≃ SetDomain (symmetricExtensionDomain U P.val Γ.val F.val G) :=
    symmetricQuotientEquiv U P R Γ F G hR.1 hG
  let : Nonempty (SetDomain (symmetricExtensionDomain U P.val Γ.val F.val G)) :=
    Nonempty.map e inferInstance
  refine ⟨?_⟩
  intro φ hφ
  have hs := Theory.models S.Model 𝗭𝗙 hφ
  change φ.Eval ![] Empty.elim at hs
  have he := (eval_membershipIso e (symmetricQuotientEquiv_mem_iff U P R Γ F G hR.1 hG) φ ![] Empty.elim).mp hs
  have hf : (fun x : Empty ↦ e (Empty.elim x)) = Empty.elim := by
    funext x
    exact Empty.elim x
  simpa only [models_iff, Semiformula.Realize, Function.comp_def, Matrix.empty_eq, hf] using he

theorem symmetricQuotientValue_check (P R Γ F one : SetDomain U) (G : V)
    (hR : IsForcingPoset P R) (hΓ : IsForcingAutomorphismGroup P R Γ)
    (hF : IsNormalSubgroupFilter P Γ F) (hone : IsForcingTop P R one)
    (hG : IsGroundForcingGeneric U P.val R.val G) (x : SetDomain U) :
    (symmetricQuotientValue U P R Γ F G hR.1 hG
      ((groundSymmetricContext U P R Γ F one G hR hΓ hF hone hG).check x)).val = x.val := by
  change nameValue G (checkName one x).val = x.val
  rw [checkName_val U]
  apply nameValue_checkName
  have ht : one ∈ {p : SetDomain U | p.val ∈ G} :=
    externalForcingFilter_top ((groundForcingGeneric_iff_external U P R G hG.1.1).mp hG).1 hone
  exact ht

end TransitiveZF
end ZFVP
