import ZFVP.ModelTheory.SchmerlDeadEndTheorem
import ZFVP.ModelTheory.CohenVopenkaConsistency
import ZFVP.ModelTheory.ForcingProperEndExtension
import ZFVP.ModelTheory.ForcingCheckedTruth

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory Entailment

/-- The exact consistency premise supplies a countable ZF+VP model without Choice. -/
theorem exists_countable_zfVP_notChoice_model (h : Consistent zfVPTheory) :
    ∃ (M : Type) (_ : SetStructure M) (_ : Nonempty M) (_ : Countable M)
      (_ : M↓[ℒₛₑₜ] ⊧* 𝗭𝗙),
      (∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := M) φ) ∧ ¬InternalChoice M := by
  obtain ⟨M, hne, hstr, hM⟩ := satisfiable_iff.mp
    (Theory.small_satisfiable_of_consistent (consistent_zfVP_notChoice_notDC h))
  let := hne
  let := hstr
  let hEQ : M↓[ℒₛₑₜ] ⊧* (𝗘𝗤 ℒₛₑₜ) := ⟨fun φ hφ ↦ hM.models_set
    (Or.inr (Or.inr (Or.inl (ZermeloFraenkel.axiom_of_equality φ hφ))))⟩
  let N := QuotNormalize M
  have hN : N↓[ℒₛₑₜ] ⊧* zfVPNotChoiceNotDCTheory :=
    (inferInstance : N ≡ₑ[ℒₛₑₜ] M).modelsTheory.mpr hM
  let U := Collapse N
  have hU : U↓[ℒₛₑₜ] ⊧* zfVPNotChoiceNotDCTheory :=
    (inferInstance : U ≡ₑ[ℒₛₑₜ] N).modelsTheory.mpr hN
  let hZF : U↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := ⟨fun φ hφ ↦ hU.models_set (Or.inr (Or.inr (Or.inl hφ)))⟩
  refine ⟨U, inferInstance, inferInstance, inferInstance, hZF, ?_, ?_⟩
  · intro φ
    exact (eval_vopenkaSentence φ).mp (hU.models_set (Or.inr (Or.inr (Or.inr ⟨φ, rfl⟩))))
  · have hh := hU.models_set (show (∼choiceFunctionSentence) ∈ zfVPNotChoiceNotDCTheory from Or.inl rfl)
    simpa [models_iff, Semiformula.Realize, Semiformula.Evalb] using hh

/-- The countability-essential proposition from Con(ZF+VP), with an actual
aleph-one model and no proper ZF end extension. -/
theorem countability_essential_of_consistent (h : Consistent zfVPTheory) :
    ∃ (N : Type) (_ : SetStructure N) (_ : Nonempty N) (_ : N↓[ℒₛₑₜ] ⊧* 𝗭𝗙),
      Cardinal.mk N = Cardinal.aleph 1 ∧
      (∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := N) φ) ∧
      ¬InternalChoice N ∧ IsZFDeadEnd N := by
  obtain ⟨M, hstr, hne, hcount, hZF, hVP, hAC⟩ := exists_countable_zfVP_notChoice_model h
  let := hstr
  let := hne
  let := hcount
  let := hZF
  obtain ⟨E, hVPE, hACE⟩ := countability_essential_complete M hVP hAC
  exact ⟨E.Model, inferInstance, inferInstance, inferInstance, E.card, hVPE, hACE, E.deadEnd⟩

/-- Every set-forcing extension represented by a generic quotient adds no set
to the constructed model. The dead-end conclusion also applies to arbitrary
ZF end extensions beyond this set-forcing specialization. -/
theorem countability_essential_forcing_obstruction (h : Consistent zfVPTheory) :
    ∃ (N : Type) (_ : SetStructure N) (_ : Nonempty N) (_ : N↓[ℒₛₑₜ] ⊧* 𝗭𝗙),
      Cardinal.mk N = Cardinal.aleph 1 ∧
      (∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := N) φ) ∧
      ¬InternalChoice N ∧ IsZFDeadEnd N ∧
      ∀ A : ForcingContext N, Function.Surjective A.check := by
  obtain ⟨N, hs, hn, hz, hc, hv, ha, hd⟩ := countability_essential_of_consistent h
  let := hs
  let := hn
  let := hz
  exact ⟨N, hs, hn, hz, hc, hv, ha, hd, fun A ↦ hd.surjective A.Model A.checkEmbedding⟩

end ZFVP
