import ZFVP.ModelTheory.ForcingQuotientValuation

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingExtensionDomain_nonempty (P : SetDomain U) (G : V) :
    Nonempty (SetDomain (forcingExtensionDomain U P.val G)) :=
  ⟨groundNameValue U P G ⟨∅, empty_forcingName P⟩⟩

theorem forcingExtensionDomain_models_zf (P R one : SetDomain U) (G : V)
    (hR : IsForcingPreorder P.val R.val) (hone : IsForcingTop P.val R.val one.val)
    (hG : IsGroundForcingGeneric U P.val R.val G) :
    (SetDomain (forcingExtensionDomain U P.val G))↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  let hRi : IsForcingPreorder P R := (forcingPreorder_iff U P R).mpr hR
  let hGi := (groundForcingGeneric_iff_external U P R G hG.1.1).mp hG
  let := forcingQuotient_models_zf P R _ hRi hGi one ((forcingTop_iff U P R one).mpr hone)
  let e := forcingQuotientEquiv U P R G hRi hG
  refine ⟨?_⟩
  intro φ hφ
  have hs := Theory.models (ForcingQuotient P R _ hRi hGi.1) 𝗭𝗙 hφ
  change φ.Eval ![] Empty.elim at hs
  have he := (eval_membershipIso e (forcingQuotientEquiv_mem_iff U P R G hRi hG) φ ![] Empty.elim).mp hs
  have hf : (fun x : Empty ↦ e (Empty.elim x)) = Empty.elim := by
    funext x
    exact Empty.elim x
  simpa only [models_iff, Semiformula.Realize, Function.comp_def, Matrix.empty_eq, hf] using he

theorem forcingQuotientValue_check (P R one : SetDomain U) (G : V)
    (hR : IsForcingPreorder P R) (hone : IsForcingTop P R one)
    (hG : IsGroundForcingGeneric U P.val R.val G) (x : SetDomain U) :
    (forcingQuotientValue U P R G hR hG
      (forcingCheck P R _ hR ((groundForcingGeneric_iff_external U P R G hG.1.1).mp hG).1 one hone x)).val = x.val := by
  change nameValue G (checkName one x).val = x.val
  rw [checkName_val U]
  apply nameValue_checkName
  have ht : one ∈ {p : SetDomain U | p.val ∈ G} :=
    externalForcingFilter_top ((groundForcingGeneric_iff_external U P R G hG.1.1).mp hG).1 hone
  exact ht

end TransitiveZF
end ZFVP
