import ZFVP.ModelTheory.SingularWeaklyLSCollapseDC
import ZFVP.SetTheory.VopenkaWeaklyLowenheimSkolem
import ZFVP.ModelTheory.ForcingVopenkaPreservation
import ZFVP.ModelTheory.CountableCohenVopenkaConsistency

/-! V13 Section 6.3 from its original consistency hypothesis. The singular
weakly LS collapse gives DC and preserves VP. If Choice holds there, the
omega-one Cohen symmetric model gives DC with not Choice; otherwise that
collapse extension itself is the required model. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory Entailment

theorem consistent_zfVP_DC_notChoice_of_zfVP (h : Consistent zfVPTheory) :
    Consistent zfVPDCNotChoiceTheory := by
  classical
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
  obtain ⟨κ, _, hκ, _, hsing⟩ := vopenka_singular_weaklyLSCardinal hVP (0 : U)
  obtain ⟨G, hG, _⟩ := exists_externalForcingGeneric (collapse_poset (hierarchy κ)).1
    (collapse_top (hierarchy κ)).1
  let S := collapseContext (hierarchy κ) G hG
  have hDC : InternalDependentChoice S.Model := CollapseModel.dependentChoice_of_singular_weaklyLS hκ hsing hG
  have hSVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := S.Model) φ :=
    S.vopenkaInstance (collapse_poset (hierarchy κ)) hVP
  let : Countable S.Model := S.ofName_surjective.countable
  by_cases hAC : InternalChoice S.Model
  · obtain ⟨H, hH, _⟩ := exists_externalForcingGeneric
      (countableCohen_poset (hartogsNumber (ω : S.Model)) (hartogsNumber (ω : S.Model))).1
      (countableCohen_top (hartogsNumber (ω : S.Model)) (hartogsNumber (ω : S.Model))).1
    exact Theory.consistent_of_satisfiable
      ⟨(omegaOneCohenContext H hH).Model↓[ℒₛₑₜ], omegaOneCohen_model_zfVP_DC_notChoice hAC hSVP hH⟩
  · have hmodel : S.Model↓[ℒₛₑₜ] ⊧* zfVPDCNotChoiceTheory := by
      refine ⟨?_⟩
      intro φ hφ
      rcases hφ with rfl | (rfl | (hφ | ⟨ψ, rfl⟩))
      · simpa [models_iff, Semiformula.Realize, Semiformula.Evalb] using hDC
      · simpa [models_iff, Semiformula.Realize, Semiformula.Evalb] using hAC
      · exact Theory.models S.Model 𝗭𝗙 hφ
      · exact (eval_vopenkaSentence ψ).mpr (hSVP ψ)
    exact Theory.consistent_of_satisfiable ⟨S.Model↓[ℒₛₑₜ], hmodel⟩

theorem consistent_zfVP_DC_notChoice_iff :
    Consistent zfVPDCNotChoiceTheory ↔ Consistent zfVPTheory := by
  constructor
  · intro h
    exact h.of_le (WeakerThan.ofSubset (fun _ hφ ↦ Or.inr (Or.inr hφ)))
  · exact consistent_zfVP_DC_notChoice_of_zfVP

end ZFVP


