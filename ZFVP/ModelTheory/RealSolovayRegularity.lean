import ZFVP.ModelTheory.SolovayModel
import ZFVP.SetTheory.RealRegularitySentences
import ZFVP.SetTheory.RealLebesgueTransfer

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω hκ in
theorem solovay_realBaireProperty :
    haveI := solovay_models_zf hAC hU hc hω hκ hG
    AllRealBaireProperty (SolovayHOD κ hG) := by
  have := solovay_models_zf hAC hU hc hω hκ hG
  exact allRealBaireProperty_of_internalDC
    (solovay_dependentChoice hAC hU hc hω hκ hG)
    (solovay_baireProperty hAC hU hc hω hκ hG)

include hAC hU hc hω hκ in
theorem solovay_realPerfectSetProperty :
    haveI := solovay_models_zf hAC hU hc hω hκ hG
    AllRealPerfectSetProperty (SolovayHOD κ hG) := by
  have := solovay_models_zf hAC hU hc hω hκ hG
  exact allRealPerfectSetProperty_of_internalDC
    (solovay_dependentChoice hAC hU hc hω hκ hG)
    (solovay_perfectSetProperty hAC hU hc hω hκ hG)

include hAC hU hc hω hκ in
theorem solovay_realLebesgueMeasurable :
    haveI := solovay_models_zf hAC hU hc hω hκ hG
    AllRealLebesgueMeasurable (SolovayHOD κ hG) := by
  have := solovay_models_zf hAC hU hc hω hκ hG
  exact allRealLebesgueMeasurable_of_cantor
    (solovay_dependentChoice hAC hU hc hω hκ hG)
    (solovay_lebesgueMeasurable hAC hU hc hω hκ hG)

include hAC hU hc hω hκ in
/-- The paper's regularity lemma for actual internal Dedekind reals, over arbitrary grounds. -/
theorem solovay_realRegularity :
    haveI := solovay_models_zf hAC hU hc hω hκ hG
    (SolovayHOD κ hG)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 ∧
    InternalDependentChoice (SolovayHOD κ hG) ∧
    AllRealLebesgueMeasurable (SolovayHOD κ hG) ∧
    AllRealBaireProperty (SolovayHOD κ hG) ∧
    AllRealPerfectSetProperty (SolovayHOD κ hG) ∧
    hartogsNumber (ω : SolovayHOD κ hG) = solovayCheck hAC hU hc hω hκ hG κ := by
  have := solovay_models_zf hAC hU hc hω hκ hG
  exact ⟨inferInstance, solovay_dependentChoice hAC hU hc hω hκ hG,
    solovay_realLebesgueMeasurable hAC hU hc hω hκ hG,
    solovay_realBaireProperty hAC hU hc hω hκ hG,
    solovay_realPerfectSetProperty hAC hU hc hω hκ hG,
    solovay_hartogsNumber_omega hAC hU hc hω hκ hG⟩

end ZFVP
