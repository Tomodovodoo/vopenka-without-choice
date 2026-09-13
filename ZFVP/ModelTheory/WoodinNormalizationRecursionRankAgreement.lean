import ZFVP.ModelTheory.WoodinNormalizationRuleRankAgreement
import ZFVP.ModelTheory.WoodinSourceEndpointAgreement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSupercompact.rank_woodinNormalizationRec_val {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ θ : SetDomain (hierarchy Ω), IsOrdinal θ →
      (woodinNormalizationRec θ).val = woodinNormalizationRec θ.val := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  intro θ hθ
  let := hθ
  let α := succ θ
  let := (TransitiveZF.ordinal_iff (hierarchy Ω) α).mp (inferInstance : IsOrdinal α)
  let f := woodinNormalizationHistory α
  have hvalue (t : SetDomain (hierarchy Ω)) (ht : t ∈ α) :
      (woodinNormalizationRec t).val = f.val ‘ t.val := by
    rw [← TransitiveZF.value_val_total (hierarchy Ω) f t]
    congr 1
    exact (woodinNormalizationHistory_value ht).symm
  have hall := transfinite_induction
    (fun β : V ↦ β ∈ α.val → f.val ‘ β = woodinNormalizationRec β) (by definability) ?_
  · let := (TransitiveZF.ordinal_iff (hierarchy Ω) θ).mp hθ
    exact (hvalue θ (mem_succ_self θ)).trans
      (hall (IsOrdinal.toOrdinal θ.val) (mem_succ_self θ))
  intro β ih hβα
  let b : SetDomain (hierarchy Ω) := ⟨β, (hierarchy_transitive Ω).mem_trans hβα α.property⟩
  have hb : IsOrdinal b := (TransitiveZF.ordinal_iff (hierarchy Ω) b).mpr inferInstance
  let := hb
  have hprev : ∀ i ∈ b, (woodinNormalizationRec i).val = woodinNormalizationRec i.val := by
    intro i hib
    have hiα : i ∈ α := IsOrdinal.toIsTransitive.mem_trans hib hβα
    let := IsOrdinal.of_mem hib
    let := (TransitiveZF.ordinal_iff (hierarchy Ω) i).mp (inferInstance : IsOrdinal i)
    exact (hvalue i hiα).trans (ih (IsOrdinal.toOrdinal i.val) hib hiα)
  have hm : (woodinNormalizationHistory b).val = woodinNormalizationHistory b.val := by
    unfold woodinNormalizationHistory
    exact TransitiveZF.definableGraph_val (hierarchy Ω) b _ _ _ _ hprev
  have hp := TransitiveZF.woodinIterationPrefixes_val_of_previous (hierarchy Ω) b
    (fun i hi ↦ hΩ.rank_woodinIterationRec_val hAC i (IsOrdinal.of_mem hi))
  have he := hΩ.rank_woodinNormalizationRule_val hAC b (woodinIterationPrefix b)
    (woodinIterationCardinalPrefix b) (woodinNormalizationHistory b) hb hp.1 hp.2 hm
  rw [← hvalue b hβα, woodinNormalizationRec_rule b, he, hp.1, hp.2, hm]
  exact (woodinNormalizationRec_rule (β : V)).symm

theorem IsWoodinSupercompact.rank_woodinNormalizationHistory_val {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ θ : SetDomain (hierarchy Ω), IsOrdinal θ →
      (woodinNormalizationHistory θ).val = woodinNormalizationHistory θ.val := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  intro θ hθ
  let := hθ
  unfold woodinNormalizationHistory
  exact TransitiveZF.definableGraph_val (hierarchy Ω) θ _ _ _ _
    (fun i hi ↦ hΩ.rank_woodinNormalizationRec_val hAC i (IsOrdinal.of_mem hi))
end ZFVP
