import ZFVP.ModelTheory.SymmetricExtensionZF

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def groundSymmetricNameValue (P Γ F : SetDomain U) (G : V)
    (τ : {x : SetDomain U // IsHereditarilySymmetricName P Γ F x}) :
    SetDomain (symmetricExtensionDomain U P.val Γ.val F.val G) :=
  ⟨nameValue G τ.val.val, (mem_symmetricExtensionDomain_iff _ _ _ _ _ _).mpr
    ⟨τ.val.val, τ.val.property, (hereditarilySymmetricName_iff U P Γ F τ.val).mp τ.property, rfl⟩⟩

theorem ground_symmetricForcingFormula_truth (P R Γ F : SetDomain U) (G : V)
    (hR : IsForcingPreorder P R) (hG : IsGroundForcingGeneric U P.val R.val G)
    {n : ℕ} (φ : SetTheorySemisentence n)
    (v : Fin n → {x : SetDomain U // IsHereditarilySymmetricName P Γ F x}) :
    φ.Evalb (fun i ↦ groundSymmetricNameValue U P Γ F G (v i)) ↔
      ∃ p ∈ G, p ∈ (symmetricForcingFormula P R Γ F φ (standardTuple (fun i ↦ (v i).val))).val := by
  let hGi := (groundForcingGeneric_iff_external U P R G hG.1.1).mp hG
  let e := symmetricQuotientEquiv U P R Γ F G hR hG
  have he := eval_membershipIso e (symmetricQuotientEquiv_mem_iff U P R Γ F G hR hG) φ
    (ClassForcingQuotient.assignment P R _ hR hGi.1 _ _ v) Empty.elim
  have hf : (fun x : Empty ↦ e (Empty.elim x)) = Empty.elim := by
    funext x
    exact Empty.elim x
  have hb : e ∘ ClassForcingQuotient.assignment P R _ hR hGi.1 _ _ v =
      (fun i ↦ groundSymmetricNameValue U P Γ F G (v i)) := rfl
  rw [hb, show e ∘ Empty.elim = Empty.elim from hf] at he
  exact he.symm.trans ((ClassForcingQuotient.formula_truth P R _ hR hGi
    (IsHereditarilySymmetricName P Γ F) (by definability) (fun _ h ↦ h.1) φ v).trans
      (genericMeets_val_iff U G _))

end TransitiveZF
end ZFVP
