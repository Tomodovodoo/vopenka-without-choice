import ZFVP.ModelTheory.CountableCohenDependentChoice
import ZFVP.ModelTheory.CountableCohenNotChoice
import ZFVP.ModelTheory.SymmetricVopenkaPreservation
import ZFVP.ModelTheory.SVCVopenkaRestoration
import ZFVP.SetTheory.ChoiceDictionary
import Foundation.FirstOrder.SetTheory.LoewenheimSkolem

/-! Lemma lem:omega1-Cohen: over an arbitrary model of ZFC and the Vopenka scheme, the
countable-support Cohen symmetric extension at omega_1 satisfies ZF, every Vopenka
instance, dependent choice, and the failure of choice. Hence Con(ZFC+VP) gives
Con(ZF+VP+DC+not AC). -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory Entailment

def zfVPDCNotChoiceTheory : Theory ℒₛₑₜ :=
  insert dependentChoiceSentence (insert (∼choiceFunctionSentence) zfVPTheory)

theorem omegaOneCohen_model_zfVP_DC_notChoice {V : Type*} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (hAC : InternalChoice V)
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    {G : Set V}
    (hG : IsExternalForcingGeneric (countableCohenConditions (hartogsNumber (ω : V)) (hartogsNumber (ω : V)))
      (countableCohenOrder (hartogsNumber (ω : V)) (hartogsNumber (ω : V))) G) :
    (omegaOneCohenContext G hG).Model↓[ℒₛₑₜ] ⊧* zfVPDCNotChoiceTheory := by
  let S := omegaOneCohenContext G hG
  refine ⟨?_⟩
  intro φ hφ
  rcases hφ with rfl | (rfl | (hφ | ⟨ψ, rfl⟩))
  · have hh := OmegaOneCohenModel.model_dependentChoice hG hAC
    simpa [models_iff, Semiformula.Realize, Semiformula.Evalb] using hh
  · have hh := OmegaOneCohenModel.model_not_choice hG (countableChoice_of_internalChoice hAC)
    simpa [models_iff, Semiformula.Realize, Semiformula.Evalb] using hh
  · exact Theory.models S.Model 𝗭𝗙 hφ
  · exact (eval_vopenkaSentence ψ).mpr (S.vopenkaInstance hVP ψ)

theorem consistent_zfVP_DC_notChoice (h : Consistent zfcVPTheory) :
    Consistent zfVPDCNotChoiceTheory := by
  obtain ⟨M, hne, hstr, hM⟩ := satisfiable_iff.mp (Theory.small_satisfiable_of_consistent h)
  let := hne
  let := hstr
  let hEQ : M↓[ℒₛₑₜ] ⊧* (𝗘𝗤 ℒₛₑₜ) := ⟨fun φ hφ ↦ hM.models_set
    (Or.inl (Or.inl (ZermeloFraenkel.axiom_of_equality φ hφ)))⟩
  let N := QuotNormalize M
  have hN : N↓[ℒₛₑₜ] ⊧* zfcVPTheory := (inferInstance : N ≡ₑ[ℒₛₑₜ] M).modelsTheory.mpr hM
  let U := Collapse N
  have hU : U↓[ℒₛₑₜ] ⊧* zfcVPTheory := (inferInstance : U ≡ₑ[ℒₛₑₜ] N).modelsTheory.mpr hN
  let hZF : U↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := ⟨fun φ hφ ↦ hU.models_set (Or.inl (Or.inl hφ))⟩
  let hACm : U↓[ℒₛₑₜ] ⊧* 𝗔𝗖 := ⟨fun φ hφ ↦ hU.models_set (Or.inl (Or.inr hφ))⟩
  have hAC : InternalChoice U := internalChoice_of_models_ac
  have hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := U) φ := by
    intro φ
    exact (eval_vopenkaSentence φ).mp (hU.models_set (Or.inr ⟨φ, rfl⟩))
  obtain ⟨G, hG, _⟩ := exists_externalForcingGeneric
    (countableCohen_poset (hartogsNumber (ω : U)) (hartogsNumber (ω : U))).1
    (countableCohen_top (hartogsNumber (ω : U)) (hartogsNumber (ω : U))).1
  exact Theory.consistent_of_satisfiable
    ⟨(omegaOneCohenContext G hG).Model↓[ℒₛₑₜ], omegaOneCohen_model_zfVP_DC_notChoice hAC hVP hG⟩

end ZFVP
