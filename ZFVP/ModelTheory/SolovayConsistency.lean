import ZFVP.ModelTheory.SolovayTheory
import ZFVP.ModelTheory.SolovayCorollaryUnconditional
import ZFVP.SetTheory.VopenkaMeasurableRanks
import ZFVP.ModelTheory.WoodinSparseRestorationTheorem
import Foundation.FirstOrder.SetTheory.LoewenheimSkolem

/-! The full Solovay consistency corollary from consistency of ZF + VP.

Woodin restoration supplies consistency of ZFC + VP. A countable normalized
model of that theory has a measurable ordinal by the direct VP rank argument.
Countability supplies the Levy generic, and the unconditional Solovay theorem
then supplies a model of every sentence of the full target theory.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory Entailment

theorem solovay_model_theory {V : Type*} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]  {κ U : V} [IsOrdinal κ]
    (hAC : InternalChoice V) (hU : IsNonprincipalSetUltrafilter κ U)
    (hc : IsOrdinalComplete κ U) (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
    {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ) :
    (SolovayHOD κ hG)↓[ℒₛₑₜ] ⊧* solovayTheory := by
  let S := SolovayHOD κ hG
  let := solovay_models_zf hAC hU hc hω hκ hG
  obtain ⟨_, hVPS, hDC, hLM, hBP, hPSP, hnotAC, hωone, hUS, hcS⟩ :=
    Unconditional.solovay_corollary hAC hU hc hω hκ hG hVP
  have hmeasure : ∃ W : S,
      IsNonprincipalSetUltrafilter (hartogsNumber (ω : S)) W ∧
      IsOrdinalComplete (hartogsNumber (ω : S)) W := by
    refine ⟨solovayUltrafilter hAC hU hc hω hκ hG, ?_⟩
    simpa only [hωone] using And.intro hUS hcS
  refine ⟨?_⟩
  intro φ hφ
  rcases hφ with rfl | (rfl | (rfl | (rfl | (rfl | (rfl | (hφ | ⟨ψ, rfl⟩))))))
  · exact (Defined.eval_iff (φ := dependentChoiceSentence) (![] : Fin 0 → S)).mpr hDC
  · exact (Defined.eval_iff (φ := lebesgueMeasurableSentence) (![] : Fin 0 → S)).mpr hLM
  · exact (Defined.eval_iff (φ := bairePropertySentence) (![] : Fin 0 → S)).mpr hBP
  · exact (Defined.eval_iff (φ := perfectSetPropertySentence) (![] : Fin 0 → S)).mpr hPSP
  · have hnot := mt (Defined.eval_iff (φ := choiceFunctionSentence) (![] : Fin 0 → S)).mp hnotAC
    simpa [models_iff, Semiformula.Realize, Semiformula.Evalb] using hnot
  · exact (Defined.eval_iff (φ := omegaOneCompleteUltrafilterSentence) (![] : Fin 0 → S)).mpr hmeasure
  · exact Theory.models S 𝗭𝗙 hφ
  · exact (eval_vopenkaSentence ψ).mpr (hVPS ψ)

/-- No countable ground, measurable ordinal, ultrafilter or generic is supplied
as an input: all are obtained from consistency of ZFC + VP. -/
theorem consistent_solovay_of_consistent_zfcVP (h : Consistent zfcVPTheory) :
    Consistent solovayTheory := by
  obtain ⟨M, hne, hstr, hM⟩ := satisfiable_iff.mp (Theory.small_satisfiable_of_consistent h)
  let := hne
  let := hstr
  let hEQ : M↓[ℒₛₑₜ] ⊧* (𝗘𝗤 ℒₛₑₜ) := ⟨fun φ hφ ↦ hM.models_set
    (Or.inl (Or.inl (ZermeloFraenkel.axiom_of_equality φ hφ)))⟩
  let N := QuotNormalize M
  have hN : N↓[ℒₛₑₜ] ⊧* zfcVPTheory := (inferInstance : N ≡ₑ[ℒₛₑₜ] M).modelsTheory.mpr hM
  let V := Collapse N
  have hV : V↓[ℒₛₑₜ] ⊧* zfcVPTheory := (inferInstance : V ≡ₑ[ℒₛₑₜ] N).modelsTheory.mpr hN
  let hZF : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := ⟨fun φ hφ ↦ hV.models_set (Or.inl (Or.inl hφ))⟩
  let hACm : V↓[ℒₛₑₜ] ⊧* 𝗔𝗖 := ⟨fun φ hφ ↦ hV.models_set (Or.inl (Or.inr hφ))⟩
  have hAC : InternalChoice V := internalChoice_of_models_ac
  have hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ := by
    intro φ
    exact (eval_vopenkaSentence φ).mp (hV.models_set (Or.inr ⟨φ, rfl⟩))
  obtain ⟨κ, _, _, hmeas⟩ := vopenka_measurable_rankCriterion_unbounded hVP (ω : V)
  let := hmeas.1.1
  obtain ⟨U, hU, hc⟩ := hmeas.2.2
  obtain ⟨G, hG, _⟩ := exists_externalForcingGeneric
    (levyCollapse_poset κ).1 (levyCollapse_top κ).1
  exact Theory.consistent_of_satisfiable
    ⟨(SolovayHOD κ hG)↓[ℒₛₑₜ], solovay_model_theory hAC hU hc hmeas.2.1 hmeas.1 hG hVP⟩

/-- The paper's full Solovay consistency implication, starting with ZF + VP. -/
theorem consistent_solovay_of_consistent_zfVP (h : Consistent zfVPTheory) :
    Consistent solovayTheory :=
  consistent_solovay_of_consistent_zfcVP (consistent_zfcVP_of_consistent_zfVP_woodin h)

end ZFVP
