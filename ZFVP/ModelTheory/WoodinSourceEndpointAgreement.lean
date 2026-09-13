import ZFVP.ModelTheory.WoodinSourcePresentationRankAgreement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The recursion computed in the endpoint rank agrees at every internal ordinal.
No supercompact cardinal inside that rank is assumed. -/
theorem IsWoodinSupercompact.rank_woodinIterationRec_val {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    letI := hδ.inaccessible.1
    letI := rankDomain_nonempty hδ.inaccessible.2.1
    letI := hδ.inaccessible.rankCriterion.models_zf
    ∀ t : SetDomain (hierarchy δ), IsOrdinal t →
      (woodinIterationRec t).val = woodinIterationRec t.val := by
  let := hδ.inaccessible.1
  let := rankDomain_nonempty hδ.inaccessible.2.1
  let := hδ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive δ
  intro t ht
  let := (TransitiveZF.ordinal_iff (hierarchy δ) t).mp ht
  have htδ : t.val ∈ δ := ordinal_mem_hierarchy_iff.mp t.property
  obtain ⟨η, hηδ, _, he⟩ := woodinIterationRec_eventually_rank_eq hδ hAC htδ
  exact he δ hηδ hδ.inaccessible t rfl

/-- The complete source tables computed in the endpoint rank are the ambient
tables at the same index, including the seed and the completed-stage row. -/
theorem IsWoodinSupercompact.rank_woodinSourcePresentation_val {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    letI := hδ.inaccessible.1
    letI := rankDomain_nonempty hδ.inaccessible.2.1
    letI := hδ.inaccessible.rankCriterion.models_zf
    ∀ t : SetDomain (hierarchy δ), IsOrdinal t →
      (woodinSourceCode t (woodinIterationPrefix t)).val =
        woodinSourceCode t.val (woodinIterationPrefix t.val) ∧
      (woodinSourceCardinals t (woodinIterationCardinalPrefix t)).val =
        woodinSourceCardinals t.val (woodinIterationCardinalPrefix t.val) ∧
      (woodinSourceCode (succ t) (kpair.π₁ (woodinIterationRec t))).val =
        woodinSourceCode (succ t.val) (kpair.π₁ (woodinIterationRec t.val)) ∧
      (woodinSourceCardinals (succ t) (kpair.π₂ (woodinIterationRec t))).val =
        woodinSourceCardinals (succ t.val) (kpair.π₂ (woodinIterationRec t.val)) := by
  let := hδ.inaccessible.1
  let := rankDomain_nonempty hδ.inaccessible.2.1
  let := hδ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive δ
  intro t ht
  let := (TransitiveZF.ordinal_iff (hierarchy δ) t).mp ht
  have htδ : t.val ∈ δ := ordinal_mem_hierarchy_iff.mp t.property
  obtain ⟨η, hηδ, _, he⟩ := woodinSourcePresentation_eventually_rank_eq hδ hAC htδ
  exact he δ hηδ hδ.inaccessible t rfl

/-- Every source prefix and completed source table strictly below the endpoint
is a set of the endpoint rank. This includes all projection and replacement maps. -/
theorem IsWoodinSupercompact.woodinSourcePresentation_mem_hierarchy {δ α : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) (hαδ : α ∈ δ) :
    woodinSourceCode α (woodinIterationPrefix α) ∈ hierarchy δ ∧
    woodinSourceCardinals α (woodinIterationCardinalPrefix α) ∈ hierarchy δ ∧
    woodinSourceCode (succ α) (kpair.π₁ (woodinIterationRec α)) ∈ hierarchy δ ∧
    woodinSourceCardinals (succ α) (kpair.π₂ (woodinIterationRec α)) ∈ hierarchy δ := by
  let := hδ.inaccessible.1
  let := rankDomain_nonempty hδ.inaccessible.2.1
  let := hδ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive δ
  let := IsOrdinal.of_mem hαδ
  let t : SetDomain (hierarchy δ) := ⟨α, ordinal_mem_hierarchy_iff.mpr hαδ⟩
  have ht : IsOrdinal t := (TransitiveZF.ordinal_iff (hierarchy δ) t).mpr inferInstance
  obtain ⟨hP, hK, hC, hL⟩ := hδ.rank_woodinSourcePresentation_val hAC t ht
  exact ⟨hP ▸ (woodinSourceCode t (woodinIterationPrefix t)).property,
    hK ▸ (woodinSourceCardinals t (woodinIterationCardinalPrefix t)).property,
    hC ▸ (woodinSourceCode (succ t) (kpair.π₁ (woodinIterationRec t))).property,
    hL ▸ (woodinSourceCardinals (succ t) (kpair.π₂ (woodinIterationRec t))).property⟩

end ZFVP
