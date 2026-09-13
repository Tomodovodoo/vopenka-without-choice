import ZFVP.ModelTheory.SolovayConsistency
import ZFVP.ModelTheory.RealSolovayTheory
import ZFVP.ModelTheory.RealSolovayRegularity

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory Entailment

theorem realSolovay_model_theory {V : Type*} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] {κ U : V} [IsOrdinal κ]
    (hAC : InternalChoice V) (hU : IsNonprincipalSetUltrafilter κ U)
    (hc : IsOrdinalComplete κ U) (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
    {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ) :
    (SolovayHOD κ hG)↓[ℒₛₑₜ] ⊧* realSolovayTheory := by
  let := solovay_models_zf hAC hU hc hω hκ hG
  obtain ⟨_, hVPS, hDC, _, _, _, hnotAC, hωone, hUS, hcS⟩ :=
    Unconditional.solovay_corollary hAC hU hc hω hκ hG hVP
  apply models_realSolovayTheory hVPS hDC
    (solovay_realLebesgueMeasurable hAC hU hc hω hκ hG)
    (solovay_realBaireProperty hAC hU hc hω hκ hG)
    (solovay_realPerfectSetProperty hAC hU hc hω hκ hG) hnotAC
  refine ⟨solovayUltrafilter hAC hU hc hω hκ hG, ?_⟩
  simpa only [hωone] using And.intro hUS hcS

/-- No countable ground, measurable ordinal, ultrafilter or generic is supplied
as an input: all are obtained from consistency of ZFC + VP. -/
theorem consistent_realSolovay_of_consistent_zfcVP (h : Consistent zfcVPTheory) :
    Consistent realSolovayTheory := by
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
    ⟨(SolovayHOD κ hG)↓[ℒₛₑₜ], realSolovay_model_theory hAC hU hc hmeas.2.1 hmeas.1 hG hVP⟩

/-- The paper's full Solovay consistency implication, starting with ZF + VP. -/
theorem consistent_realSolovay_of_consistent_zfVP (h : Consistent zfVPTheory) :
    Consistent realSolovayTheory :=
  consistent_realSolovay_of_consistent_zfcVP (consistent_zfcVP_of_consistent_zfVP_woodin h)

end ZFVP
