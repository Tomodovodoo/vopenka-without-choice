import ZFVP.ModelTheory.WoodinNormalizationSuccessorRankAgreement
import ZFVP.ModelTheory.WoodinNormalizationInverseRankAgreement
import ZFVP.ModelTheory.WoodinSparseInitialRankAgreement
import ZFVP.ModelTheory.WoodinNormalizationConstruction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSupercompact.rank_woodinNormalizationRule_val {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ t s K m : SetDomain (hierarchy Ω), IsOrdinal t →
      s.val = woodinIterationPrefix t.val → K.val = woodinIterationCardinalPrefix t.val →
      m.val = woodinNormalizationHistory t.val →
      (woodinNormalizationRule t s K m).val = woodinNormalizationRule t.val s.val K.val m.val := by
  classical
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  intro t s K m ht hs hK hm
  let := ht
  let := (TransitiveZF.ordinal_iff (hierarchy Ω) t).mp ht
  have htΩ : t.val ∈ Ω := ordinal_mem_hierarchy_iff.mp t.property
  have hex := woodinIterationExit hΩ hAC
  have hst := fun i (hi : i ∈ t.val) ↦
    (hex.2.1 i (IsOrdinal.toIsTransitive.mem_trans hi htΩ)).1
  have hp := woodinIterationPrefix_of_stages hst
  have hnf := woodinNormalizationHistory_prefix_family hst
    (fun i hi ↦ woodinNormalizationHistory_family hΩ hAC i
      (IsOrdinal.toIsTransitive.mem_trans hi htΩ))
  have hn : IsForcingNormalizationFamily t.val s.val m.val := by
    simpa only [hs, hm] using hnf
  have hclosed := hΩ.inaccessible.rankCriterion.2.2.1
  by_cases hz : t = ∅
  · subst t
    simp only [woodinNormalizationRule, TransitiveZF.empty_val]
    exact hΩ.rank_woodinNormalizationInitialMap_val hAC
  have hzv : t.val ≠ ∅ := by
    intro hh
    exact hz (Subtype.ext (hh.trans (TransitiveZF.empty_val (hierarchy Ω)).symm))
  have hsuccval : (succ (⋃ˢ t)).val = succ (⋃ˢ t.val) := by
    rw [TransitiveZF.succ_val, TransitiveZF.sUnion_val]
  by_cases hsucc : t = succ (⋃ˢ t)
  · have hsuccv := (congrArg Subtype.val hsucc).trans hsuccval
    have hk : ⋃ˢ t.val ∈ t.val := (congrArg (fun θ : V ↦ (⋃ˢ t.val) ∈ θ) hsuccv).mpr (mem_succ_self (⋃ˢ t.val))
    have hstage : IsWoodinStage (woodinIterationStage s.val K.val (⋃ˢ t).val) := by
      simpa only [hs, hK, TransitiveZF.sUnion_val] using hp.stage _ hk
    have hnorm : IsForcingNormalizationFamily (succ (⋃ˢ t).val) s.val m.val := by
      simpa only [TransitiveZF.sUnion_val, ← hsuccv] using hn
    have he := hΩ.rank_woodinNormalizationSuccessorMap_val (⋃ˢ t) s K m hstage hnorm
    simp only [woodinNormalizationRule, ite_eq_right hz, ite_eq_left hsucc, ite_eq_right hzv, ite_eq_left hsuccv]
    simpa only [TransitiveZF.sUnion_val] using he
  have hnsv : t.val ≠ succ (⋃ˢ t.val) := by
    intro hh
    exact hsucc (Subtype.ext (hh.trans hsuccval.symm))
  have hiiff : IsChoicelessInaccessible (woodinLimitCardinal K) ↔
      IsChoicelessInaccessible (woodinLimitCardinal K.val) := by
    rw [rank_choicelessInaccessible_iff hclosed, TransitiveZF.woodinLimitCardinal_val]
  by_cases hi : IsChoicelessInaccessible (woodinLimitCardinal K)
  · simp only [woodinNormalizationRule, ite_eq_right hz, ite_eq_right hsucc, ite_eq_right hzv, ite_eq_right hnsv,
      ite_eq_left hi, ite_eq_left (hiiff.mp hi)]
    exact rank_forcingNormalizationDirectMap_val hclosed t s m
  · have hnI := fun hc ↦ hi (hiiff.mpr hc)
    simp only [woodinNormalizationRule, ite_eq_right hz, ite_eq_right hsucc, ite_eq_right hzv, ite_eq_right hnsv,
      ite_eq_right hi, ite_eq_right hnI]
    exact hΩ.rank_woodinNormalizationInverseMap_val hAC t s K m ht
      ((IsOrdinal.subset_iff.mp (empty_subset t.val)).resolve_left (fun he ↦ hzv he.symm)) (ordinal_limit_of_not_successor hnsv) hs hK hnI hn
end ZFVP

