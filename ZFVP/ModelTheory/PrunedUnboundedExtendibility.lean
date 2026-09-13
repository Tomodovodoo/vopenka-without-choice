import ZFVP.ModelTheory.RankBerkeleyPruning
import ZFVP.SetTheory.VopenkaPruningUE

/-! OH pruning with the nonzero rank-Berkeley convention: adjoining UE
and absence of rank-Berkeley cardinals preserves consistency of ZF+VP. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory Entailment

def zfVPNoRankBerkeleyTheory : Theory ℒₛₑₜ :=
  insert (∼nonzeroRankBerkeleyExistenceSentence) zfVPTheory

def zfUEVPNoRankBerkeleyTheory : Theory ℒₛₑₜ :=
  insert (∼nonzeroRankBerkeleyExistenceSentence) zfUEVPTheory

theorem prunedVP_models_UE (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* zfVPNoRankBerkeleyTheory] : V↓[ℒₛₑₜ] ⊧* zfUEVPNoRankBerkeleyTheory := by
  let hZF : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := ⟨fun φ hφ ↦
    Theory.models V zfVPNoRankBerkeleyTheory (Or.inr (Or.inl hφ))⟩
  have hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ := by
    intro φ
    exact (eval_vopenkaSentence φ).mp
      (Theory.models V zfVPNoRankBerkeleyTheory (Or.inr (Or.inr ⟨φ, rfl⟩)))
  have hneg : V↓[ℒₛₑₜ] ⊧ ∼nonzeroRankBerkeleyExistenceSentence :=
    Theory.models V zfVPNoRankBerkeleyTheory (Or.inl rfl)
  have hno : ∀ μ : V, ¬IsNonzeroRankBerkeley μ := by
    simpa [models_iff, nonzeroRankBerkeleyExistenceSentence] using hneg
  refine ⟨?_⟩
  intro φ hφ
  rcases hφ with rfl | (hφ | ⟨n, rfl⟩)
  · exact hneg
  · exact Theory.models V zfVPNoRankBerkeleyTheory (Or.inr hφ)
  · apply (eval_unboundedExtendibilitySentence (n + 1)).mpr
    intro ξ hξ
    let := hξ
    exact vopenka_no_rankBerkeley_unboundedExtendibility hVP hno n ξ

theorem prunedUE_weaker_prunedVP : zfUEVPNoRankBerkeleyTheory ⪯ zfVPNoRankBerkeleyTheory := by
  let heq : 𝗘𝗤 ℒₛₑₜ ⪯ zfVPNoRankBerkeleyTheory := WeakerThan.ofSubset
    (fun φ hφ ↦ Or.inr (Or.inl (ZermeloFraenkel.axiom_of_equality φ hφ)))
  apply WeakerThan.ofAxm!
  intro φ hφ
  apply SetTheory.provable_of_models.{0} zfVPNoRankBerkeleyTheory φ
  intro V _ _ _
  let := prunedVP_models_UE V
  exact Theory.models V zfUEVPNoRankBerkeleyTheory hφ

theorem consistent_pruned_UE (h : Consistent zfVPTheory) : Consistent zfUEVPNoRankBerkeleyTheory :=
  (consistent_no_nonzeroRankBerkeley h).of_le prunedUE_weaker_prunedVP

theorem consistent_pruned_UE_iff : Consistent zfUEVPNoRankBerkeleyTheory ↔ Consistent zfVPTheory := by
  constructor
  · intro h
    exact h.of_le (WeakerThan.ofSubset (fun _ hφ ↦ Or.inr (Or.inl hφ)))
  · exact consistent_pruned_UE

end ZFVP
