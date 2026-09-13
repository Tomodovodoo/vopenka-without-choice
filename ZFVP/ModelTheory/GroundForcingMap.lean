import ZFVP.ModelTheory.GroundFormulaTruth
import ZFVP.ModelTheory.CodedMembershipEmbedding
import ZFVP.SetTheory.ElementaryForcing

/-! Elementarity of a coded ground map preserves valuation equality in a common generic. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsCodedMembershipEmbedding

variable {U W f : V} [IsTransitive U] [IsTransitive W]
variable [Nonempty (SetDomain U)] [Nonempty (SetDomain W)]
variable [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [(SetDomain W)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def groundNameMap (h : IsCodedMembershipEmbedding U W f) (P : SetDomain U)
    (σ : ForcingName P) : ForcingName (h.toFunction P) :=
  ⟨h.toFunction σ.val, (h.toElementaryMap.forcingName_iff P σ.val).mp σ.property⟩

theorem ground_formula_forward (h : IsCodedMembershipEmbedding U W f) (P R : SetDomain U) (G : V)
    (hR : IsForcingPreorder P.val R.val)
    (hGU : IsGroundForcingGeneric U P.val R.val G)
    (hGW : IsGroundForcingGeneric W (f ‘ P.val) (f ‘ R.val) G)
    (hfix : ∀ p ∈ G, f ‘ p = p) {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → ForcingName P)
    (hv : φ.Evalb (fun i ↦ TransitiveZF.groundNameValue U P G (v i))) :
    φ.Evalb (fun i ↦ TransitiveZF.groundNameValue W (h.toFunction P) G (h.groundNameMap P (v i))) := by
  obtain ⟨p, hpG, hpF⟩ := (TransitiveZF.ground_forcingFormula_truth U P R G hR hGU φ v).mp hv
  let p' : SetDomain U := ⟨p, (inferInstance : IsTransitive U).mem_trans hpF
    (forcingFormula P R φ (standardTuple (fun i ↦ (v i).val))).property⟩
  have hr := (h.toElementaryMap.forcingPreorder_iff P R).mp ((TransitiveZF.forcingPreorder_iff U P R).mpr hR)
  apply (TransitiveZF.ground_forcingFormula_truth W (h.toFunction P) (h.toFunction R) G
    ((TransitiveZF.forcingPreorder_iff W _ _).mp hr) hGW φ (fun i ↦ h.groundNameMap P (v i))).mpr
  have hm := (h.toElementaryMap.forcingFormula_tuple_iff P R p' φ (fun i ↦ (v i).val)).mp hpF
  refine ⟨f ‘ p, (hfix p hpG).symm ▸ hpG, ?_⟩
  exact hm

theorem nameValue_eq_of_eq (h : IsCodedMembershipEmbedding U W f) (P R : SetDomain U) (G : V)
    (hR : IsForcingPreorder P.val R.val)
    (hGU : IsGroundForcingGeneric U P.val R.val G)
    (hGW : IsGroundForcingGeneric W (f ‘ P.val) (f ‘ R.val) G)
    (hfix : ∀ p ∈ G, f ‘ p = p) (σ τ : SetDomain U)
    (hσ : IsForcingName P.val σ.val) (hτ : IsForcingName P.val τ.val)
    (he : nameValue G σ.val = nameValue G τ.val) :
    nameValue G (f ‘ σ.val) = nameValue G (f ‘ τ.val) := by
  let σ' : ForcingName P := ⟨σ, (TransitiveZF.forcingName_iff U P σ).mpr hσ⟩
  let τ' : ForcingName P := ⟨τ, (TransitiveZF.forcingName_iff U P τ).mpr hτ⟩
  have he' : TransitiveZF.groundNameValue U P G σ' = TransitiveZF.groundNameValue U P G τ' := Subtype.ext he
  have ht := h.ground_formula_forward P R G hR hGU hGW hfix
    (.rel Language.Set.Rel.eq ![.bvar 0, .bvar 1]) ![σ', τ']
    (by simpa [Semiformula.Evalb, Structure.rel] using he')
  have ht' : TransitiveZF.groundNameValue W (h.toFunction P) G (h.groundNameMap P σ') =
      TransitiveZF.groundNameValue W (h.toFunction P) G (h.groundNameMap P τ') := by
    simpa [Semiformula.Evalb, Structure.rel] using ht
  exact congrArg Subtype.val ht'

end IsCodedMembershipEmbedding
end ZFVP
