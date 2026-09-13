import ZFVP.ModelTheory.CohenVopenkaConsistency
import ZFVP.ModelTheory.ConsistencyTransferPassage
import ZFVP.ModelTheory.CohenSetInjectionWitness
import ZFVP.ModelTheory.SVCVopenkaRestoration
import ZFVP.SetTheory.RealSequenceCoding

/-! The basic Cohen symmetric model satisfies the rigid relation principle while failing
choice and dependent choice. The injection into finite sequences of reals times an ordinal
is proved by `cohenSetInjectionInput`; no injection or restoration premise is used below. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory Entailment

/-- Every set of the basic Cohen symmetric model has a rigid relation. -/
theorem cohen_model_rigidRelationPrinciple {V : Type*}
    [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (hAC : InternalChoice V)
    {G : Set V} (hG : IsExternalForcingGeneric (cohenConditions (ω : V)) (cohenOrder (ω : V)) G) :
    RigidRelationPrinciple (cohenContext (ω : V) G hG).Model := by
  intro x
  obtain ⟨γ, A, f, hγ, hA, hf, hinj, hran⟩ :=
    CohenModel.set_injection_finiteSequences_cantor_ordinal hG hAC x
  exact hasRigidRelation_of_bijection hf hinj hran
    (hasRigidRelation_of_subset_finiteSequences_prod hγ hA)

def zfVPRigidNotChoiceNotDCTheory : Theory ℒₛₑₜ :=
  insert rigidRelationSentence zfVPNotChoiceNotDCTheory

/-- The Cohen model preserves VP and satisfies RR, not AC, and not DC. -/
theorem cohen_model_zfVP_rigid_notChoice_notDC {V : Type*}
    [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable V] (hAC : InternalChoice V)
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    {G : Set V} (hG : IsExternalForcingGeneric (cohenConditions (ω : V)) (cohenOrder (ω : V)) G) :
    (cohenContext (ω : V) G hG).Model↓[ℒₛₑₜ] ⊧* zfVPRigidNotChoiceNotDCTheory := by
  have hbase := cohen_model_zfVP_notChoice_notDC hVP hG
  refine ⟨?_⟩
  intro φ hφ
  rcases hφ with rfl | hφ
  · have hh := cohen_model_rigidRelationPrinciple hAC hG
    simpa [models_iff, Semiformula.Realize, Semiformula.Evalb] using hh
  · exact hbase.models_set hφ

/-- The positive rigid-relation consistency result from the proved ZFC+VP input. -/
theorem consistent_zfVP_rigid_notChoice_notDC_of_zfcVP
    (h : Consistent zfcVPTheory) : Consistent zfVPRigidNotChoiceNotDCTheory := by
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
  obtain ⟨G, hG, _⟩ := exists_externalForcingGeneric (cohen_poset (ω : U)).1 (cohen_top (ω : U)).1
  exact Theory.consistent_of_satisfiable
    ⟨(cohenContext (ω : U) G hG).Model↓[ℒₛₑₜ],
      cohen_model_zfVP_rigid_notChoice_notDC hAC hVP hG⟩

/-- Finite restoration gives the positive rigid-relation consistency result from ZF+VP.
The Cohen injection premise is discharged by the constructed injection theorem. -/
theorem consistent_zfVP_rigid_notChoice_notDC (hFR : FiniteRestorationInput)
    (h : Consistent zfVPTheory) : Consistent zfVPRigidNotChoiceNotDCTheory :=
  consistent_zfVP_rigid_notChoice_notDC_of_zfcVP
    (consistent_zfcVP_of_consistent_zfVP hFR h)

end ZFVP
