import ZFVP.ModelTheory.WoodinSparseRowRankAgreement
import ZFVP.ModelTheory.WoodinSparseInverseMapRankAgreement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSupercompact.rank_woodinSparseRecodingRowRule_val {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ t c m : SetDomain (hierarchy Ω), IsOrdinal t →
      c.val = woodinSparsePrefixCode t.val →
      m.val = woodinRecodingMaps (woodinSparseRecodingHistory t.val) →
      (woodinSparseRecodingRowRule t c m).val = woodinSparseRecodingRowRule t.val c.val m.val := by
  classical
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  intro t c m ht hc hm
  let := ht
  let := (TransitiveZF.ordinal_iff (hierarchy Ω) t).mp ht
  by_cases hz : t = ∅
  · subst t
    simp only [woodinSparseRecodingRowRule, TransitiveZF.empty_val]
    exact hΩ.rank_woodinSparseRecodingInitialRow_val hAC
  have hzv : t.val ≠ ∅ := by
    intro hh
    exact hz (Subtype.ext (hh.trans (TransitiveZF.empty_val (hierarchy Ω)).symm))
  have hsuccval : (succ (⋃ˢ t)).val = succ (⋃ˢ t.val) := by
    rw [TransitiveZF.succ_val, TransitiveZF.sUnion_val]
  by_cases hsucc : t = succ (⋃ˢ t)
  · have hsuccv := (congrArg Subtype.val hsucc).trans hsuccval
    have hk : ⋃ˢ t.val ∈ t.val :=
      (congrArg (fun θ : V ↦ (⋃ˢ t.val) ∈ θ) hsuccv).mpr (mem_succ_self (⋃ˢ t.val))
    have hk' : IsOrdinal (⋃ˢ t) := (TransitiveZF.ordinal_iff (hierarchy Ω) (⋃ˢ t)).mpr
      ((TransitiveZF.sUnion_val (hierarchy Ω) t).symm ▸ IsOrdinal.of_mem hk)
    have hc' : c.val = woodinSparsePrefixCode (succ (⋃ˢ t).val) := by
      simpa only [TransitiveZF.sUnion_val, ← hsuccv] using hc
    have hm' : m.val = woodinRecodingMaps (woodinSparseRecodingHistory (succ (⋃ˢ t).val)) := by
      simpa only [TransitiveZF.sUnion_val, ← hsuccv] using hm
    simp only [woodinSparseRecodingRowRule, ite_eq_right hz, ite_eq_left hsucc,
      ite_eq_right hzv, ite_eq_left hsuccv]
    simpa only [TransitiveZF.sUnion_val] using
      hΩ.rank_woodinSparseRecodingSuccessorRow_actual_val hAC (⋃ˢ t) c m hk' hc' hm'
  have hnsv : t.val ≠ succ (⋃ˢ t.val) := by
    intro hh
    exact hsucc (Subtype.ext (hh.trans hsuccval.symm))
  have hp := TransitiveZF.woodinIterationPrefixes_val_of_previous (hierarchy Ω) t
    (fun i hi ↦ hΩ.rank_woodinIterationRec_val hAC i (IsOrdinal.of_mem hi))
  have hiiff : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix t)) ↔
      IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix t.val)) := by
    rw [rank_choicelessInaccessible_iff hΩ.inaccessible.rankCriterion.2.2.1,
      TransitiveZF.woodinLimitCardinal_val, hp.2]
  by_cases hi : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix t))
  · simp only [woodinSparseRecodingRowRule, ite_eq_right hz, ite_eq_right hsucc,
      ite_eq_right hzv, ite_eq_right hnsv, ite_eq_left hi, ite_eq_left (hiiff.mp hi)]
    exact hΩ.rank_woodinSparseRecodingDirectRow_val hAC t c m ht
  · have hn := fun hh ↦ hi (hiiff.mpr hh)
    have hlim := ordinal_limit_of_not_successor hnsv
    obtain ⟨_, _, hP, hR⟩ := TransitiveZF.woodinSparseCompletedInverse_val_of_actual_prefix
      hΩ hAC t c hc hzv hlim hn
    have he := TransitiveZF.woodinSparseCompletedInverseMap_val_of_actual_prefix
      hΩ hAC t c m hc hm hzv hlim hn
    simp only [woodinSparseRecodingRowRule, ite_eq_right hz, ite_eq_right hsucc,
      ite_eq_right hzv, ite_eq_right hnsv, ite_eq_right hi, ite_eq_right hn,
      woodinSparseRecodingInverseRow, TransitiveZF.kpair_val, hP, hR, he]
end ZFVP

