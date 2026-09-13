import ZFVP.ModelTheory.CohenDedekindFinite
import ZFVP.ModelTheory.SymmetricVopenkaPreservation
import ZFVP.ModelTheory.CodedZFVPExternal
import ZFVP.SetTheory.ChoiceDictionary
import Foundation.FirstOrder.SetTheory.LoewenheimSkolem

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory Entailment

def zfVPNotChoiceNotDCTheory : Theory ℒₛₑₜ :=
  insert (∼choiceFunctionSentence) (insert (∼dependentChoiceSentence) zfVPTheory)

theorem cohen_model_zfVP_notChoice_notDC {V : Type*} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable V]
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    {G : Set V} (hG : IsExternalForcingGeneric (cohenConditions (ω : V)) (cohenOrder (ω : V)) G) :
    (cohenContext (ω : V) G hG).Model↓[ℒₛₑₜ] ⊧* zfVPNotChoiceNotDCTheory := by
  let S := cohenContext (ω : V) G hG
  refine ⟨?_⟩
  intro φ hφ
  rcases hφ with rfl | (rfl | (hφ | ⟨ψ, rfl⟩))
  · have hh := cohen_model_not_choice hG
    simpa [models_iff, Semiformula.Realize, Semiformula.Evalb] using hh
  · have hh := cohen_model_not_dependentChoice hG
    simpa [models_iff, Semiformula.Realize, Semiformula.Evalb] using hh
  · exact Theory.models S.Model 𝗭𝗙 hφ
  · exact (eval_vopenkaSentence ψ).mpr (S.vopenkaInstance hVP ψ)

theorem consistent_zfVP_notChoice_notDC (h : Consistent zfVPTheory) :
    Consistent zfVPNotChoiceNotDCTheory := by
  obtain ⟨M, hne, hstr, hM⟩ := satisfiable_iff.mp (Theory.small_satisfiable_of_consistent h)
  let := hne
  let := hstr
  let hEQ : M↓[ℒₛₑₜ] ⊧* (𝗘𝗤 ℒₛₑₜ) := ⟨fun φ hφ ↦ hM.models_set
    (Or.inl (ZermeloFraenkel.axiom_of_equality φ hφ))⟩
  let N := QuotNormalize M
  have hN : N↓[ℒₛₑₜ] ⊧* zfVPTheory := (inferInstance : N ≡ₑ[ℒₛₑₜ] M).modelsTheory.mpr hM
  let U := Collapse N
  have hU : U↓[ℒₛₑₜ] ⊧* zfVPTheory := (inferInstance : U ≡ₑ[ℒₛₑₜ] N).modelsTheory.mpr hN
  let hZF : U↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := ⟨fun φ hφ ↦ hU.models_set (Or.inl hφ)⟩
  have hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := U) φ := by
    intro φ
    exact (eval_vopenkaSentence φ).mp (hU.models_set (Or.inr ⟨φ, rfl⟩))
  obtain ⟨G, hG, _⟩ := exists_externalForcingGeneric (cohen_poset (ω : U)).1 (cohen_top (ω : U)).1
  exact Theory.consistent_of_satisfiable
    ⟨(cohenContext (ω : U) G hG).Model↓[ℒₛₑₜ], cohen_model_zfVP_notChoice_notDC hVP hG⟩

theorem consistent_zfVP_notChoice_notDC_iff :
    Consistent zfVPNotChoiceNotDCTheory ↔ Consistent zfVPTheory := by
  constructor
  · intro h
    exact h.of_le (WeakerThan.ofSubset (fun _ hφ ↦ Or.inr (Or.inr hφ)))
  · exact consistent_zfVP_notChoice_notDC

end ZFVP



