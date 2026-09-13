import ZFVP.ModelTheory.WoodinSparseRuleRankAgreement
import ZFVP.ModelTheory.TransitiveZFSparseRecodingHistory

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSupercompact.rank_woodinSparseRecodingRec_val {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ θ : SetDomain (hierarchy Ω), IsOrdinal θ →
      (woodinSparseRecodingRec θ).val = woodinSparseRecodingRec θ.val := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  intro θ hθ
  let := hθ
  let α := succ θ
  let := (TransitiveZF.ordinal_iff (hierarchy Ω) α).mp (inferInstance : IsOrdinal α)
  let f := woodinSparseRecodingHistory α
  have hvalue (t : SetDomain (hierarchy Ω)) (ht : t ∈ α) :
      (woodinSparseRecodingRec t).val = f.val ‘ t.val := by
    rw [← TransitiveZF.value_val_total (hierarchy Ω) f t]
    congr 1
    exact (woodinSparseRecodingHistory_value ht).symm
  have hall := transfinite_induction
    (fun β : V ↦ β ∈ α.val → f.val ‘ β = woodinSparseRecodingRec (β : V)) (by definability) ?_
  · let := (TransitiveZF.ordinal_iff (hierarchy Ω) θ).mp hθ
    exact (hvalue θ (mem_succ_self θ)).trans
      (hall (IsOrdinal.toOrdinal θ.val) (mem_succ_self θ))
  intro β ih hβα
  let b : SetDomain (hierarchy Ω) := ⟨β, (hierarchy_transitive Ω).mem_trans hβα α.property⟩
  have hb : IsOrdinal b := (TransitiveZF.ordinal_iff (hierarchy Ω) b).mpr inferInstance
  let := hb
  have hprev : ∀ i ∈ b, (woodinSparseRecodingRec i).val = woodinSparseRecodingRec i.val := by
    intro i hib
    have hiα : i ∈ α := IsOrdinal.toIsTransitive.mem_trans hib hβα
    let := IsOrdinal.of_mem hib
    let := (TransitiveZF.ordinal_iff (hierarchy Ω) i).mp (inferInstance : IsOrdinal i)
    exact (hvalue i hiα).trans (ih (IsOrdinal.toOrdinal i.val) hib hiα)
  have hH := TransitiveZF.woodinSparseRecodingHistory_val_of_stages (hierarchy Ω) b hprev
  let H := woodinSparseRecodingHistory b
  let m := woodinRecodingMaps H
  let c := forcingRecodedCode b (woodinNormalizedPrefixCode b)
    (woodinRecodingCarriers H) (woodinRecodingOrders H) m
  have hm : m.val = woodinRecodingMaps (woodinSparseRecodingHistory b.val) := by
    dsimp only [m, H]
    rw [TransitiveZF.woodinRecodingMaps_val, hH]
  have hc : c.val = woodinSparsePrefixCode b.val := by
    dsimp only [c, m, H]
    rw [TransitiveZF.forcingRecodedCode_val, TransitiveZF.woodinRecodingCarriers_val,
      TransitiveZF.woodinRecodingOrders_val, TransitiveZF.woodinRecodingMaps_val, hH,
      (hΩ.rank_woodinNormalizedCode_val hAC b hb).1]
    rfl
  have he := hΩ.rank_woodinSparseRecodingRowRule_val hAC b c m hb hc hm
  rw [← hvalue b hβα, woodinSparseRecodingRec_rule b]
  change (woodinSparseRecodingRowRule b c m).val = woodinSparseRecodingRec (β : V)
  rw [he, hc, hm]
  exact (woodinSparseRecodingRec_rule (β : V)).symm

theorem IsWoodinSupercompact.rank_woodinSparseRecodingHistory_val {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ θ : SetDomain (hierarchy Ω), IsOrdinal θ →
      (woodinSparseRecodingHistory θ).val = woodinSparseRecodingHistory θ.val := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  intro θ hθ
  let := hθ
  exact TransitiveZF.woodinSparseRecodingHistory_val_of_stages (hierarchy Ω) θ
    (fun i hi ↦ hΩ.rank_woodinSparseRecodingRec_val hAC i (IsOrdinal.of_mem hi))
end ZFVP

