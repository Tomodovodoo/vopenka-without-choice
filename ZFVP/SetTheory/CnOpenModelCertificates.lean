import ZFVP.Syntax.SigmaOneOpenModels
import ZFVP.Syntax.ZFOpenAxiomSet
import ZFVP.SetTheory.CnSigmaClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem Cn.membershipFormulaFamily_mem {γ : V} (hγ : Cn 1 γ) :
    (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy γ := by
  obtain ⟨F, hF, he⟩ := hγ.sigmaOne_witness sigmaOneMembershipFamilyFormula_sigmaOne
    (![] : Fin 0 → V) (fun i ↦ Fin.elim0 i)
    ⟨formulaFamily membershipLanguageCode ∅, (eval_sigmaOneMembershipFamilyFormula _).mpr rfl⟩
  exact (eval_sigmaOneMembershipFamilyFormula F).mp he ▸ hF

theorem Cn.zfOpenAxiomCodes_mem {γ : V} (hγ : Cn 1 γ) :
    (zfOpenAxiomCodes : V) ∈ hierarchy γ := by
  let := hγ.ordinal
  exact subset_mem_hierarchy_limit hγ.successor_closed hγ.membershipFormulaFamily_mem
    (show (zfOpenAxiomCodes : V) ⊆ formulaFamily membershipLanguageCode ∅ from sep_subset)

theorem Cn.openModel_certificate {γ C Z : V} (hγ : Cn 1 γ)
    (hC : C ∈ hierarchy γ) (hZ : Z ∈ hierarchy γ) (hm : SatisfiesOpenCodes C Z) :
    ∃ U ∈ hierarchy γ, boundedOpenModelCertificate.Evalb ![U, C, Z] := by
  exact hγ.sigmaOne_witness (.bounded boundedOpenModelCertificate_bounded) ![C, Z]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hC, hZ])
    ((boundedOpenModelCertificate_exists C Z).mpr hm)

theorem Cn.internalZF_certificate {γ C : V} (hγ : Cn 1 γ)
    (hC : C ∈ hierarchy γ) (hm : IsInternalZFModel C) :
    ∃ U ∈ hierarchy γ, boundedOpenModelCertificate.Evalb ![U, C, zfOpenAxiomCodes] :=
  hγ.openModel_certificate hC hγ.zfOpenAxiomCodes_mem hm.satisfies_open_codes

end ZFVP
