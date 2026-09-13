import ZFVP.Syntax.EndExtensionMembershipSatisfaction
import ZFVP.Syntax.SigmaOneOpenModels
import ZFVP.SetTheory.EndExtensionLevy

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def setDomainEndExtension {V : Type*} [SetStructure V] (U : V) [hU : IsTransitive U] :
    MembershipEndExtension (SetDomain U) V where
  toFun := Subtype.val
  injective := Subtype.val_injective
  mem_iff _ _ := Iff.rfl
  endExtension x y hy := ⟨⟨y, hU.mem_trans hy x.property⟩, hy, rfl⟩

variable {V W : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem MembershipEndExtension.satisfiesOpenCodes_downward (j : MembershipEndExtension V W)
    (C Z : V) (h : SatisfiesOpenCodes (j C) (j Z)) : SatisfiesOpenCodes C Z := by
  obtain ⟨x, hx⟩ := h.1.nonempty
  obtain ⟨y, hy, _⟩ := j.endExtension C x hx
  refine ⟨⟨y, hy⟩, ?_⟩
  intro n φ hnφ
  have hp : ⟨j n, j φ⟩ₖ ∈ j Z := by
    rw [← j.map_kpair]
    exact (j.mem_iff _ _).mpr hnφ
  obtain ⟨hv, hs⟩ := h.2 (j n) (j φ) hp
  have hc := (j.membershipFormulaCode_iff n φ).mp hv
  refine ⟨hc, fun b hb ↦ (j.membershipSatisfies_iff C n φ b).mp ?_⟩
  have hb' : j b ∈ (j C) ^ (j n) := by
    rw [← j.map_finiteFunctionSet C hc.context]
    exact (j.mem_iff _ _).mpr hb
  exact hs (j b) hb'

theorem MembershipEndExtension.satisfiesOpenCodes_iff (j : MembershipEndExtension V W)
    (C Z : V) : SatisfiesOpenCodes (j C) (j Z) ↔ SatisfiesOpenCodes C Z := by
  refine ⟨j.satisfiesOpenCodes_downward C Z, ?_⟩
  intro h
  have ht := j.sigma_one_upward sigmaOneOpenModelFormula_sigmaOne ![C, Z]
    ((eval_sigmaOneOpenModelFormula C Z).mpr h)
  have hv : (fun i ↦ j (![C, Z] i)) = ![j C, j Z] := by
    funext i
    exact Fin.cases rfl (fun k ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) k) i
  rw [hv] at ht
  exact (eval_sigmaOneOpenModelFormula (j C) (j Z)).mp ht

theorem transitiveZF_openModel_certificate {U : V} [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (C Z : SetDomain U) (hm : SatisfiesOpenCodes C.val Z.val) :
    ∃ T ∈ U, boundedOpenModelCertificate.Evalb ![T, C.val, Z.val] := by
  let j := setDomainEndExtension U
  have hi := j.satisfiesOpenCodes_downward C Z hm
  obtain ⟨T, hT⟩ := (boundedOpenModelCertificate_exists C Z).mpr hi
  have ht := j.bounded_elementary boundedOpenModelCertificate_bounded ![T, C, Z] |>.mp hT
  have hv : (fun i ↦ j (![T, C, Z] i)) = ![T.val, C.val, Z.val] := by
    funext i
    exact Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases rfl (fun m ↦ Fin.elim0 m) l) k) i
  rw [hv] at ht
  exact ⟨T.val, T.property, ht⟩

theorem transitiveZF_membershipFormulaFamily_mem (U : V) [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] :
    (formulaFamily membershipLanguageCode ∅ : V) ∈ U := by
  have he := (setDomainEndExtension U).map_membershipFormulaFamily
  exact he ▸ (formulaFamily (membershipLanguageCode : SetDomain U) ∅).property

end ZFVP
