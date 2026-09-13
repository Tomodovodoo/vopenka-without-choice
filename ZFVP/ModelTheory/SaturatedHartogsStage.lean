import ZFVP.ModelTheory.WoodinInverseStageBounds
import ZFVP.ModelTheory.SaturatedHartogsFormulas
import ZFVP.ModelTheory.WoodinStageUniform
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def saturatedHartogsStageAtFormula : SetTheorySemisentence 6 :=
  f“z P R o κ δ. !woodinStageCodeFormula z
    (!twoStepConditionsFormula P R (!saturatedHartogsPosetNameFormula P R o κ δ) (!isEmpty))
    (!twoStepOrderFormula P R (!saturatedHartogsPosetNameFormula P R o κ δ)
      (!saturatedHartogsOrderNameFormula P R o κ δ) (!isEmpty)) (!kpair.dfn o (!isEmpty)) δ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The Hartogs-collapse stage at a supplied saturation and restoration cutoff.
Its definition alone does not assert that the cutoff restores dependent choice. -/
noncomputable def saturatedHartogsStageAt (P R one κ δ : V) : V :=
  woodinStageCode (twoStepConditions P R (saturatedHartogsPosetName P R one κ δ) ∅)
    (twoStepOrder P R (saturatedHartogsPosetName P R one κ δ)
      (saturatedHartogsOrderName P R one κ δ) ∅) ⟨one, ∅⟩ₖ δ

instance saturatedHartogsStageAtFormula_defined :
    ℒₛₑₜ-function₅[V] saturatedHartogsStageAt via saturatedHartogsStageAtFormula :=
  ⟨fun v ↦ by simp [saturatedHartogsStageAtFormula, saturatedHartogsStageAt]⟩

theorem saturatedHartogsPosetName_isName (P R one κ δ : V) :
    IsForcingName P (saturatedHartogsPosetName P R one κ δ) :=
  forcingSaturatedName_isName _ _ _ _
theorem woodinInverseSourceCode_stageAt (θ s K : V) :
    woodinIterationStage (woodinInverseSourceCode θ s K) (woodinInverseCardinalNext θ s K) θ =
    saturatedHartogsStageAt (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseCodeTop θ s) (woodinLimitCardinal K) (forcingInverseSourceCutoff θ s (woodinLimitCardinal K)) := by
  simp only [woodinIterationStage, woodinInverseSourceCode, woodinInverseCardinalNext,
    forcingInverseSourceCollapseCode, forcingInverseCollapseCode, forcingInverseTwoStepCode,
    forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeP_code, forcingCodeR_code,
    forcingCodet_code, forcingFamilyNext_new, forcingInverseCollapseName, forcingInverseRestorationName,
    forcingInverseCodePoset, forcingInverseCodeOrder, forcingInverseCodeTop, forcingInverseHartogsName,
    saturatedHartogsStageAt, saturatedHartogsPosetName, saturatedHartogsOrderName]


end ZFVP


