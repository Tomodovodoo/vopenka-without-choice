import ZFVP.ModelTheory.ForcingExtensionZF

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ground_forcingFormula_truth (P R : SetDomain U) (G : V)
    (hR : IsForcingPreorder P.val R.val) (hG : IsGroundForcingGeneric U P.val R.val G)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → ForcingName P) :
    φ.Evalb (fun i ↦ groundNameValue U P G (v i)) ↔
      ∃ p ∈ G, p ∈ (forcingFormula P R φ (standardTuple (fun i ↦ (v i).val))).val := by
  let hRi := (forcingPreorder_iff U P R).mpr hR
  let hGi := (groundForcingGeneric_iff_external U P R G hG.1.1).mp hG
  let e := forcingQuotientEquiv U P R G hRi hG
  have he := eval_membershipIso e (forcingQuotientEquiv_mem_iff U P R G hRi hG) φ
    (forcingQuotientAssignment P R _ hRi hGi.1 v) Empty.elim
  have hf : (fun x : Empty ↦ e (Empty.elim x)) = Empty.elim := by
    funext x
    exact Empty.elim x
  have hb : e ∘ forcingQuotientAssignment P R _ hRi hGi.1 v =
      (fun i ↦ groundNameValue U P G (v i)) := rfl
  rw [hb, show e ∘ Empty.elim = Empty.elim from hf] at he
  exact he.symm.trans ((forcingFormula_quotient_truth P R _ hRi hGi φ v).trans
    (genericMeets_val_iff U G _))

end TransitiveZF
end ZFVP
