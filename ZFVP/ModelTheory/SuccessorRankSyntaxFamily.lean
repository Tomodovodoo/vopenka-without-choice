import ZFVP.ModelTheory.SuccessorRankPairPreimages
import ZFVP.SetTheory.CnSigmaClosure
import ZFVP.Syntax.SigmaOneMembershipFamily

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem Cn.membershipFormulaFamily_mem {δ : V} (hδ : Cn 1 δ) :
    (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy δ := by
  obtain ⟨F, hF, he⟩ := hδ.sigmaOne_witness sigmaOneMembershipFamilyFormula_sigmaOne
    ![] (Fin.elim0 ·) ⟨formulaFamily membershipLanguageCode ∅,
      (eval_sigmaOneMembershipFamilyFormula _).mpr rfl⟩
  exact (eval_sigmaOneMembershipFamilyFormula F).mp he ▸ hF

theorem successorRankEmbedding_value_membershipFamily {δ ε f : V}
    (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (h : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) f) :
    f ‘ (formulaFamily membershipLanguageCode ∅ : V) = formulaFamily membershipLanguageCode ∅ := by
  have he := (successorRankEmbedding_sigma_iff hδ hε h sigmaOneMembershipFamilyFormula_sigmaOne
    ![formulaFamily membershipLanguageCode ∅] (by simpa using hδ.membershipFormulaFamily_mem)).mp
      ((eval_sigmaOneMembershipFamilyFormula _).mpr rfl)
  have hv : (fun i ↦ f ‘ (![formulaFamily membershipLanguageCode ∅] i)) =
      ![f ‘ (formulaFamily membershipLanguageCode ∅ : V)] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
  rw [hv] at he
  exact (eval_sigmaOneMembershipFamilyFormula _).mp he

end ZFVP
