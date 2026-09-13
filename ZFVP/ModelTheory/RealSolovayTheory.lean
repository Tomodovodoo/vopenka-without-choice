import ZFVP.ModelTheory.SolovayTheory
import ZFVP.SetTheory.RealRegularitySentences
import ZFVP.SetTheory.RealCaratheodory

/-! The Solovay target with regularity quantified over internal Dedekind reals. -/
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def realSolovayTheory : Theory ℒₛₑₜ :=
  insert dependentChoiceSentence
    (insert realLebesgueMeasurableSentence
      (insert realBairePropertySentence
        (insert realPerfectSetPropertySentence
          (insert (∼choiceFunctionSentence)
            (insert omegaOneCompleteUltrafilterSentence zfVPTheory)))))

theorem models_realSolovayTheory {V : Type*} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (hDC : InternalDependentChoice V) (hLM : AllRealLebesgueMeasurable V)
    (hBP : AllRealBaireProperty V) (hPSP : AllRealPerfectSetProperty V)
    (hnotAC : ¬ InternalChoice V)
    (hmeasure : ∃ U : V, IsNonprincipalSetUltrafilter (hartogsNumber (ω : V)) U ∧
      IsOrdinalComplete (hartogsNumber (ω : V)) U) :
    V↓[ℒₛₑₜ] ⊧* realSolovayTheory := by
  refine ⟨?_⟩
  intro φ hφ
  rcases hφ with rfl | (rfl | (rfl | (rfl | (rfl | (rfl | (hφ | ⟨ψ, rfl⟩))))))
  · exact (Defined.eval_iff (φ := dependentChoiceSentence) (![] : Fin 0 → V)).mpr hDC
  · exact (Defined.eval_iff (φ := realLebesgueMeasurableSentence) (![] : Fin 0 → V)).mpr hLM
  · exact (Defined.eval_iff (φ := realBairePropertySentence) (![] : Fin 0 → V)).mpr hBP
  · exact (Defined.eval_iff (φ := realPerfectSetPropertySentence) (![] : Fin 0 → V)).mpr hPSP
  · have hnot := mt (Defined.eval_iff (φ := choiceFunctionSentence) (![] : Fin 0 → V)).mp hnotAC
    simpa [models_iff, Semiformula.Realize, Semiformula.Evalb] using hnot
  · exact (Defined.eval_iff (φ := omegaOneCompleteUltrafilterSentence) (![] : Fin 0 → V)).mpr hmeasure
  · exact Theory.models V 𝗭𝗙 hφ
  · exact (eval_vopenkaSentence ψ).mpr (hVP ψ)

end ZFVP
