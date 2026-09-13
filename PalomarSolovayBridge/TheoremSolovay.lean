import PalomarSolovayBridge.TargetDictionary

namespace PalomarSolovayBridge
open PalomarBridge LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Every conjunct of the independent Solovay model has exactly the source meaning. -/
theorem model_iff_source {M : Type} [SetStructure M] [Nonempty M] :
    SolovayModel (fun x y : M => x ∈ y) ↔ M↓[ℒₛₑₜ] ⊧* ZFVP.realSolovayTheory := by
  constructor
  · rintro ⟨hzf, hvp, hdc, hnac, hlm, hbp, hpsp, hmeasure⟩
    let : M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := isZF_iff_models.mp hzf
    exact ZFVP.models_realSolovayTheory (coding_vopenka_iff.mp hvp)
      (PalomarDCBridge.dependentChoice_iff_internal.mp hdc) (allLM_iff.mp hlm)
      (allBP_iff.mp hbp) (allPSP_iff.mp hpsp)
      (PalomarDCBridge.failureOfChoice_iff_internal.mp hnac) (omegaOneMeasure_iff.mp hmeasure)
  · intro hm
    let hzf : M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := ⟨fun p hp => hm.models_set
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp)))))))⟩
    have hv : M↓[ℒₛₑₜ] ⊧* ZFVP.vopenkaTheory := ⟨fun p hp => hm.models_set
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hp)))))))⟩
    refine ⟨isZF_iff_models.mpr hzf, coding_vopenka_iff_models.mpr hv,
      PalomarDCBridge.dependentChoice_iff_sentence.mpr (hm.models_set (Or.inl rfl)),
      PalomarDCBridge.failureOfChoice_iff_sentence.mpr (hm.models_set
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))), ?_, ?_, ?_, ?_⟩
    · apply allLM_iff.mpr
      exact (Defined.eval_iff (φ := ZFVP.realLebesgueMeasurableSentence) (![] : Fin 0 → M)).mp
        (hm.models_set (Or.inr (Or.inl rfl)))
    · apply allBP_iff.mpr
      exact (Defined.eval_iff (φ := ZFVP.realBairePropertySentence) (![] : Fin 0 → M)).mp
        (hm.models_set (Or.inr (Or.inr (Or.inl rfl))))
    · apply allPSP_iff.mpr
      exact (Defined.eval_iff (φ := ZFVP.realPerfectSetPropertySentence) (![] : Fin 0 → M)).mp
        (hm.models_set (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · apply omegaOneMeasure_iff.mpr
      exact (Defined.eval_iff (φ := ZFVP.omegaOneCompleteUltrafilterSentence) (![] : Fin 0 → M)).mp
        (hm.models_set (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))

/-- Completeness identifies independent model existence with the exact consistency target. -/
theorem hasSolovayModel_iff_consistent :
    HasSolovayModel ↔ Entailment.Consistent ZFVP.realSolovayTheory := by
  rw [← satisfiable_translateTheory_iff ZFVP.realSolovayTheory (fun p hp =>
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (ZermeloFraenkel.axiom_of_equality p hp))))))))]
  constructor
  · rintro ⟨M, mem, hne, hmodel⟩
    let : SetStructure M := ⟨fun y x => mem x y⟩
    let : Nonempty M := hne
    exact ⟨M, mem, (models_translateTheory_iff _).mpr (model_iff_source.mp hmodel)⟩
  · rintro ⟨M, mem, hm⟩
    let : SetStructure M := ⟨fun y x => mem x y⟩
    let : Nonempty M := hm.1
    exact ⟨M, mem, hm.1, model_iff_source.mpr ((models_translateTheory_iff _).mp hm)⟩

/-- The existing ordinary-real Solovay consistency implication, with a completely
independent statement and all target conjunctions preserved. -/
theorem independent_solovay_reals (h : PalomarBridge.HasZFVPModel) : HasSolovayModel :=
  hasSolovayModel_iff_consistent.mpr
    (ZFVP.consistent_realSolovay_of_consistent_zfVP (PalomarBridge.hasZFVPModel_iff_consistent.mp h))

end PalomarSolovayBridge
