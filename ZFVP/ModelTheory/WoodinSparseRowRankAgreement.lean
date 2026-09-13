import ZFVP.ModelTheory.WoodinSparseDirectMapRankAgreement
import ZFVP.ModelTheory.WoodinSparseSuccessorMapRankAgreement
import ZFVP.ModelTheory.WoodinSparseInitialRankAgreement
import ZFVP.ModelTheory.WoodinSparseRecursion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSupercompact.rank_woodinSparseRecodingInitialRow_val {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    (woodinSparseRecodingInitialRow : SetDomain (hierarchy Ω)).val =
      (woodinSparseRecodingInitialRow : V) := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  obtain ⟨hP, hR, hm⟩ := hΩ.rank_woodinSparseInitial_val hAC
  simp only [woodinSparseRecodingInitialRow, TransitiveZF.kpair_val, hP, hR, hm]

theorem IsWoodinSupercompact.rank_woodinSparseRecodingDirectRow_val {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ θ c m : SetDomain (hierarchy Ω), IsOrdinal θ →
      (woodinSparseRecodingDirectRow θ c m).val = woodinSparseRecodingDirectRow θ.val c.val m.val := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  intro θ c m hθ
  let := hθ
  have hs := hΩ.inaccessible.rankCriterion.2.2.1
  simp only [woodinSparseRecodingDirectRow, TransitiveZF.kpair_val,
    TransitiveZF.woodinSparseDirectBase_val_rank Ω hs,
    TransitiveZF.woodinSparseDirectOrder_val_rank Ω hs,
    hΩ.rank_woodinSparseDirectMap_val hAC θ c m hθ]

theorem IsWoodinSupercompact.rank_woodinSparseRecodingSuccessorRow_val {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ k c m : SetDomain (hierarchy Ω), IsOrdinal k →
      IsWoodinStage (woodinIterationStage c.val (kpair.π₂ (woodinIterationRec k.val)) k.val) →
      IsForcingIterationCode (succ k.val) c.val →
      m.val ‘ k.val ∈ ((forcingCodeP c.val) ‘ k.val) ^
        ((forcingCodeP (woodinNormalizedStageCode k.val)) ‘ k.val) →
      (woodinSparseRecodingSuccessorRow k c m).val = woodinSparseRecodingSuccessorRow k.val c.val m.val := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  intro k c m hk ht hc hm
  obtain ⟨_, hP, hR⟩ := hΩ.rank_woodinSparseSuccessor_val hAC k c hk ht
  simp only [woodinSparseRecodingSuccessorRow, TransitiveZF.kpair_val, hP, hR,
    hΩ.rank_woodinSparseSuccessorMap_val hAC k c m hk ht hc hm]
theorem IsWoodinSupercompact.rank_woodinSparseRecodingSuccessorRow_actual_val {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ k c m : SetDomain (hierarchy Ω), IsOrdinal k →
      c.val = woodinSparsePrefixCode (succ k.val) →
      m.val = woodinRecodingMaps (woodinSparseRecodingHistory (succ k.val)) →
      (woodinSparseRecodingSuccessorRow k c m).val = woodinSparseRecodingSuccessorRow k.val c.val m.val := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  intro k c m hk hc hm
  let := hk
  let := (TransitiveZF.ordinal_iff (hierarchy Ω) k).mp hk
  have hkm : k.val ∈ Ω := ordinal_mem_hierarchy_iff.mp k.property
  have hstage : IsWoodinStage (woodinIterationStage c.val (kpair.π₂ (woodinIterationRec k.val)) k.val) := by
    rw [hc]
    have he : woodinSparsePrefixCode (succ k.val) = woodinSparseStageCode k.val := by
      unfold woodinSparsePrefixCode woodinSparseStageCode
      rw [woodinNormalizedPrefix_successor hΩ hAC hkm]
    rw [he]
    exact woodinSparseStageCode_stage hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hkm)
  obtain ⟨_, hP, hR⟩ := hΩ.rank_woodinSparseSuccessor_val hAC k c hk hstage
  simp only [woodinSparseRecodingSuccessorRow, TransitiveZF.kpair_val, hP, hR,
    hΩ.rank_woodinSparseSuccessorMap_actual_val hAC k c m hk hc hm]
end ZFVP
