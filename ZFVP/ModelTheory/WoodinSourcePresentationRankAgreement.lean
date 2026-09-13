import ZFVP.ModelTheory.TransitiveZFWoodinSourceCode
import ZFVP.ModelTheory.WoodinActualRecursionRankAgreement
import ZFVP.ModelTheory.WoodinSeedRankAgreement
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Exact rank agreement of both the source prefix and the completed source code
at an arbitrary stage below the outer Woodin-supercompact. -/
theorem woodinSourcePresentation_eventually_rank_eq {δ α : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) (hαδ : α ∈ δ) :
    ∃ η ∈ δ, α ∈ η ∧ ∀ ξ, η ∈ ξ → ∀ hξ : IsChoicelessInaccessible ξ,
      letI := hξ.1
      letI := rankDomain_nonempty hξ.2.1
      letI := hξ.rankCriterion.models_zf
      ∀ t : SetDomain (hierarchy ξ), t.val = α →
        (woodinSourceCode t (woodinIterationPrefix t)).val =
          woodinSourceCode α (woodinIterationPrefix α) ∧
        (woodinSourceCardinals t (woodinIterationCardinalPrefix t)).val =
          woodinSourceCardinals α (woodinIterationCardinalPrefix α) ∧
        (woodinSourceCode (succ t) (kpair.π₁ (woodinIterationRec t))).val =
          woodinSourceCode (succ α) (kpair.π₁ (woodinIterationRec α)) ∧
        (woodinSourceCardinals (succ t) (kpair.π₂ (woodinIterationRec t))).val =
          woodinSourceCardinals (succ α) (kpair.π₂ (woodinIterationRec α)) := by
  let := hδ.inaccessible.1
  let := IsOrdinal.of_mem hαδ
  obtain ⟨ηH, hHδ, hαH, hH⟩ := woodinIterationRec_eventually_rank_below hδ hAC
    (regularCardinal_succ_closed hδ.inaccessible.regular hαδ)
  obtain ⟨ηS, hSδ, hS⟩ := hδ.eventually_rank_woodinSeedCardinal_eq hAC
  let := IsOrdinal.of_mem hHδ
  let := IsOrdinal.of_mem hSδ
  have hbδ : ηH ∪ ηS ∈ δ := ordinal_union_mem hHδ hSδ
  let := IsOrdinal.of_mem hbδ
  let η := succ (ηH ∪ ηS)
  have hηδ : η ∈ δ := regularCardinal_succ_closed hδ.inaccessible.regular hbδ
  let := IsOrdinal.of_mem hηδ
  have hHη : ηH ∈ η := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp
    (fun z hz ↦ mem_union_iff.mpr (Or.inl hz)))
  have hSη : ηS ∈ η := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp
    (fun z hz ↦ mem_union_iff.mpr (Or.inr hz)))
  have hαη : α ∈ η := IsOrdinal.toIsTransitive.mem_trans
    (IsOrdinal.toIsTransitive.mem_trans (mem_succ_self α) hαH) hHη
  refine ⟨η, hηδ, hαη, ?_⟩
  intro ξ hηξ hξ
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  let := hierarchy_transitive ξ
  intro t ht
  have htord : IsOrdinal t := (TransitiveZF.ordinal_iff (hierarchy ξ) t).mpr (by
    rw [ht]
    infer_instance)
  let := htord
  have hh := hH ξ (IsOrdinal.toIsTransitive.mem_trans hHη hηξ) hξ
  have hr : (woodinIterationRec t).val = woodinIterationRec α := by
    simpa only [ht] using hh t (ht ▸ mem_succ_self α)
  have hp : ∀ i ∈ t, (woodinIterationRec i).val = woodinIterationRec i.val := by
    intro i hi
    exact hh i (mem_succ_iff.mpr (Or.inr (ht ▸ hi)))
  have hpre := TransitiveZF.woodinIterationPrefixes_val_of_previous (hierarchy ξ) t hp
  have hseed := hS ξ (IsOrdinal.toIsTransitive.mem_trans hSη hηξ) hξ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [TransitiveZF.woodinSourceCode_val (hierarchy ξ) _ _ htord, hpre.1, ht]
  · rw [TransitiveZF.woodinSourceCardinals_val (hierarchy ξ) _ _ htord hseed, hpre.2, ht]
  · rw [TransitiveZF.woodinSourceCode_val (hierarchy ξ) _ _ inferInstance,
      TransitiveZF.succ_val, TransitiveZF.kpair_first_val, hr, ht]
  · rw [TransitiveZF.woodinSourceCardinals_val (hierarchy ξ) _ _ inferInstance hseed,
      TransitiveZF.succ_val, TransitiveZF.kpair_second_val, hr, ht]
end ZFVP
