import ZFVP.ModelTheory.FefermanLevyReals
import ZFVP.ModelTheory.CohenVopenkaConsistency
import ZFVP.ModelTheory.SVCVopenkaRestoration

/-! Theorem thm:FL from a ZFC ground: over a countable model of ZFC and the Vopenka scheme
the Feferman-Levy symmetric extension satisfies ZF, every Vopenka instance, the failure
of choice and dependent choice, and "the reals are a countable union of countable sets".
Hence Con(ZFC+VP) gives Con(ZF+VP+not AC+not DC+that assertion). -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory Entailment

/-- The sentence: some function on omega has countable values whose union is the power set of omega. -/
def realsCountableUnionSentence : SetTheorySentence :=
  f“∃ C ∈ !function.dfn (!power.dfn (!power.dfn (!isω))) (!isω),
    (∀ n ∈ !isω, !CardLE.dfn (!value.dfn C n) (!isω)) ∧
    ∀ x, x ∈ !power.dfn (!isω) ↔ ∃ n ∈ !isω, x ∈ !value.dfn C n”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance realsCountableUnionSentence_defined :
    Defined (fun _ : Fin 0 → V ↦ RealsCountableUnionOfCountable V) realsCountableUnionSentence :=
  ⟨fun v ↦ by simp [realsCountableUnionSentence, RealsCountableUnionOfCountable, IsInternallyCountable]⟩

def zfVPFefermanLevyTheory : Theory ℒₛₑₜ :=
  insert realsCountableUnionSentence zfVPNotChoiceNotDCTheory

theorem fefermanLevy_model_theory {V : Type*} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (hAC : InternalChoice V)
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    {G : Set V} (hG : IsExternalForcingGeneric (flConditions V) (flOrder V) G) :
    (flContext G hG).Model↓[ℒₛₑₜ] ⊧* zfVPFefermanLevyTheory := by
  let S := flContext G hG
  refine ⟨?_⟩
  intro φ hφ
  rcases hφ with rfl | (rfl | (rfl | (hφ | ⟨ψ, rfl⟩)))
  · have hh := FefermanLevyModel.model_reals_countableUnion hG hAC
    exact (Defined.eval_iff (φ := realsCountableUnionSentence) (![] : Fin 0 → S.Model)).mpr hh
  · have hh := FefermanLevyModel.model_not_choice hG hAC
    simpa [models_iff, Semiformula.Realize, Semiformula.Evalb] using hh
  · have hh := FefermanLevyModel.model_not_dependentChoice hG hAC
    simpa [models_iff, Semiformula.Realize, Semiformula.Evalb] using hh
  · exact Theory.models S.Model 𝗭𝗙 hφ
  · exact (eval_vopenkaSentence ψ).mpr (S.vopenkaInstance hVP ψ)

theorem consistent_zfVP_fefermanLevy (h : Consistent zfcVPTheory) :
    Consistent zfVPFefermanLevyTheory := by
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
  obtain ⟨G, hG, _⟩ := exists_externalForcingGeneric (fl_poset (V := U)).1 (fl_top (V := U)).1
  exact Theory.consistent_of_satisfiable
    ⟨(flContext G hG).Model↓[ℒₛₑₜ], fefermanLevy_model_theory hAC hVP hG⟩

end ZFVP
