import PalomarDCBridge.Dictionary

namespace PalomarDCBridge
open PalomarBridge LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Exact identification of every conjunct with the source theory, including its
negated choice-function sentence. -/
theorem model_iff_source {M : Type} [SetStructure M] [Nonempty M] :
    (IsZF (fun x y : M => x ∈ y) ∧ Coding.Vopenka (fun x y : M => x ∈ y) ∧
      DependentChoice (fun x y : M => x ∈ y) ∧ FailureOfChoice (fun x y : M => x ∈ y)) ↔
    M↓[ℒₛₑₜ] ⊧* ZFVP.zfVPDCNotChoiceTheory := by
  constructor
  · rintro ⟨hzf, hvp, hdc, hnac⟩
    let : M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := isZF_iff_models.mp hzf
    have hv := coding_vopenka_iff_models.mp hvp
    have hd := dependentChoice_iff_sentence.mp hdc
    have ha := failureOfChoice_iff_sentence.mp hnac
    refine ⟨?_⟩
    intro p hp
    rcases hp with rfl | (rfl | (hp | hp))
    · exact hd
    · exact ha
    · exact Theory.models M 𝗭𝗙 hp
    · exact hv.models_set hp
  · intro hm
    let hzf : M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 :=
      ⟨fun p hp => hm.models_set (Or.inr (Or.inr (Or.inl hp)))⟩
    have hv : M↓[ℒₛₑₜ] ⊧* ZFVP.vopenkaTheory :=
      ⟨fun p hp => hm.models_set (Or.inr (Or.inr (Or.inr hp)))⟩
    exact ⟨isZF_iff_models.mpr hzf, coding_vopenka_iff_models.mpr hv,
      dependentChoice_iff_sentence.mpr (hm.models_set (Or.inl rfl)),
      failureOfChoice_iff_sentence.mpr (hm.models_set (Or.inr (Or.inl rfl)))⟩

/-- Completeness and equality normalization preserve the exact DC consistency claim. -/
theorem hasZFVPDCNotChoiceModel_iff_consistent :
    HasZFVPDCNotChoiceModel ↔ Entailment.Consistent ZFVP.zfVPDCNotChoiceTheory := by
  rw [← satisfiable_translateTheory_iff ZFVP.zfVPDCNotChoiceTheory
    (fun p hp => Or.inr (Or.inr (Or.inl (ZermeloFraenkel.axiom_of_equality p hp))))]
  constructor
  · rintro ⟨M, mem, hne, hzf, hvp, hdc, hnac⟩
    let : SetStructure M := ⟨fun y x => mem x y⟩
    let : Nonempty M := hne
    exact ⟨M, mem, (models_translateTheory_iff _).mpr
      (model_iff_source.mp ⟨hzf, hvp, hdc, hnac⟩)⟩
  · rintro ⟨M, mem, hm⟩
    let : SetStructure M := ⟨fun y x => mem x y⟩
    let : Nonempty M := hm.1
    exact ⟨M, mem, hm.1, model_iff_source.mpr ((models_translateTheory_iff _).mp hm)⟩

/-- Con(ZF+VP) implies Con(ZF+VP+DC+not AC), in independent membership vocabulary. -/
theorem independent_dependent_choice (h : PalomarBridge.HasZFVPModel) :
    HasZFVPDCNotChoiceModel :=
  hasZFVPDCNotChoiceModel_iff_consistent.mpr
    (ZFVP.consistent_zfVP_DC_notChoice
      (ZFVP.consistent_zfcVP_of_consistent_zfVP_woodin
        (PalomarBridge.hasZFVPModel_iff_consistent.mp h)))

end PalomarDCBridge

#print axioms PalomarDCBridge.independent_dependent_choice
