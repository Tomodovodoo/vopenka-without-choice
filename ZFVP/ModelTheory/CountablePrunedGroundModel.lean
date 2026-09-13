import ZFVP.ModelTheory.PrunedUnboundedExtendibility
import Foundation.FirstOrder.SetTheory.LoewenheimSkolem

/-! The ground model used at the start of the proof of Theorem B: from consistency of
ZF+VP, a countable set-structure model of ZF+VP+UE+"there is no nonzero rank-Berkeley
cardinal". Completeness gives some model of the pruned theory, quotienting by the
equality relation makes it a genuine set structure, and the Loewenheim-Skolem collapse
makes it countable. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory Entailment

/-- The ZF part of a model of the pruned ZF+VP+UE theory. -/
theorem prunedUEVP_models_zf (M : Type*) [SetStructure M] [Nonempty M]
    [M↓[ℒₛₑₜ] ⊧* zfUEVPNoRankBerkeleyTheory] : M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 :=
  ⟨fun _ hφ ↦ Theory.models M zfUEVPNoRankBerkeleyTheory (Or.inr (Or.inl (Or.inl hφ)))⟩

/-- Every Vopenka instance holds in a model of the pruned ZF+VP+UE theory. -/
theorem prunedUEVP_vopenkaInstance (M : Type*) [SetStructure M] [Nonempty M]
    [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [M↓[ℒₛₑₜ] ⊧* zfUEVPNoRankBerkeleyTheory] (φ : SetTheorySemisentence 2) :
    VopenkaInstance (V := M) φ :=
  (eval_vopenkaSentence φ).mp
    (Theory.models M zfUEVPNoRankBerkeleyTheory (Or.inr (Or.inl (Or.inr ⟨φ, rfl⟩))))

/-- Consistency of ZF+VP yields a countable model of ZF+VP+UE in which no nonzero
rank-Berkeley cardinal exists. This is the first step of the consistency transfer
argument for Theorem B. -/
theorem exists_countable_prunedUEVP_model (h : Consistent zfVPTheory) :
    ∃ (M : Type) (_ : SetStructure M) (_ : Nonempty M) (_ : Countable M),
      M↓[ℒₛₑₜ] ⊧* zfUEVPNoRankBerkeleyTheory := by
  obtain ⟨M, hne, hstr, hM⟩ :=
    satisfiable_iff.mp (Theory.small_satisfiable_of_consistent (consistent_pruned_UE h))
  let := hne
  let := hstr
  let hEQ : M↓[ℒₛₑₜ] ⊧* (𝗘𝗤 ℒₛₑₜ) := ⟨fun φ hφ ↦ hM.models_set
    (Or.inr (Or.inl (Or.inl (ZermeloFraenkel.axiom_of_equality φ hφ))))⟩
  let N := QuotNormalize M
  have hN : N↓[ℒₛₑₜ] ⊧* zfUEVPNoRankBerkeleyTheory :=
    (inferInstance : N ≡ₑ[ℒₛₑₜ] M).modelsTheory.mpr hM
  let U := Collapse N
  have hU : U↓[ℒₛₑₜ] ⊧* zfUEVPNoRankBerkeleyTheory :=
    (inferInstance : U ≡ₑ[ℒₛₑₜ] N).modelsTheory.mpr hN
  exact ⟨U, inferInstance, inferInstance, inferInstance, hU⟩

end ZFVP
