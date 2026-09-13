import ZFVP.ModelTheory.WoodinNormalizedCodeRankAgreement
import ZFVP.ModelTheory.WoodinSparseSuccessorRankAgreement
import ZFVP.ModelTheory.RankNormalizedBaseTwoStep
import ZFVP.ModelTheory.WoodinSparseStageInvariant

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinNormalizedStage_isWoodinStage {Ω k : V} [IsOrdinal k]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : k ∈ Ω) :
    IsWoodinStage (woodinIterationStage (woodinNormalizedStageCode k)
      (kpair.π₂ (woodinIterationRec k)) k) := by
  have hs := (((woodinIterationExit hΩ hAC).2.1 k hk).1.stage k (mem_succ_self k))
  have hv := woodinNormalizedStageCode_valid hΩ hAC hk
  have hr := woodinNormalizedStage_retraction hΩ hAC hk
  simp only [IsWoodinStage, woodinIterationStage, woodinStagePoset_code, woodinStageOrder_code,
    woodinStageTop_code, woodinStageCardinal_code] at hs ⊢
  have hone : (forcingCodet (woodinNormalizedStageCode k)) ‘ k =
      (forcingCodet (kpair.π₁ (woodinIterationRec k))) ‘ k := by
    simp only [woodinNormalizedStageCode, forcingNormalizedCode, forcingCodet_code]
  have hvec (x : V) : (fun _ : Fin 1 ↦ x) = ![x] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
  refine ⟨hv.system.order.preorder k (mem_succ_self k), hv.system.tops.top k (mem_succ_self k), hs.2.2.1, ?_, ?_⟩
  · intro p hp
    have he := woodinNormalizedStage_checked_iff hΩ hAC hk regularCardinalFormula
      ![(kpair.π₂ (woodinIterationRec k)) ‘ k] hp
    simp only [Matrix.cons_val_fin_one, hone] at he
    simpa only [hone, Matrix.cons_val_fin_one, hvec] using he.mp (hs.2.2.2.1 p (hr.inclusion p hp))
  · intro p hp
    have he := woodinNormalizedStage_checked_iff hΩ hAC hk dependentChoiceBelowFormula
      ![(kpair.π₂ (woodinIterationRec k)) ‘ k] hp
    simp only [Matrix.cons_val_fin_one, hone] at he
    simpa only [hone, Matrix.cons_val_fin_one, hvec] using he.mp (hs.2.2.2.2 p (hr.inclusion p hp))
theorem IsWoodinSupercompact.rank_woodinRecodedSuccessorMap_val {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ k c m : SetDomain (hierarchy Ω), IsOrdinal k →

      IsForcingIterationCode (succ k.val) c.val →
      m.val ‘ k.val ∈ ((forcingCodeP c.val) ‘ k.val) ^
        ((forcingCodeP (woodinNormalizedStageCode k.val)) ‘ k.val) →
      (woodinRecodedSuccessorMap k c m).val = woodinRecodedSuccessorMap k.val c.val m.val := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  intro k c m hk hc hm
  let := hk
  let := (TransitiveZF.ordinal_iff (hierarchy Ω) k).mp hk
  have hs := woodinNormalizedStage_isWoodinStage hΩ hAC (ordinal_mem_hierarchy_iff.mp k.property)
  let s := woodinNormalizedStageCode k
  let P := (forcingCodeP s) ‘ k
  let R := (forcingCodeR s) ‘ k
  let o := (forcingCodet s) ‘ k
  let κ := (kpair.π₂ (woodinIterationRec k)) ‘ k
  let δ := woodinPrefixCutoff P R o κ
  let Q := saturatedWoodinPrefixPosetName P R o κ δ
  let A := (forcingCodeP c) ‘ k
  let B := (forcingCodeR c) ‘ k
  let t := (forcingCodet c) ‘ k
  let f := m ‘ k
  have hsval : s.val = woodinNormalizedStageCode k.val := (hΩ.rank_woodinNormalizedCode_val hAC k hk).2
  have hP : P.val = (forcingCodeP (woodinNormalizedStageCode k.val)) ‘ k.val := by
    rw [TransitiveZF.value_val_total, TransitiveZF.forcingCodeP_val, hsval]
  have hR : R.val = (forcingCodeR (woodinNormalizedStageCode k.val)) ‘ k.val := by
    rw [TransitiveZF.value_val_total, TransitiveZF.forcingCodeR_val, hsval]
  have ho : o.val = (forcingCodet (woodinNormalizedStageCode k.val)) ‘ k.val := by
    rw [TransitiveZF.value_val_total, TransitiveZF.forcingCodet_val, hsval]
  have hκ : κ.val = (kpair.π₂ (woodinIterationRec k.val)) ‘ k.val := by
    rw [TransitiveZF.value_val_total, TransitiveZF.kpair_second_val, hΩ.rank_woodinIterationRec_val hAC k hk]
  have hs' : IsWoodinStage (woodinStageCode P.val R.val o.val κ.val) := by
    simpa only [hP, hR, ho, hκ, woodinIterationStage] using hs
  have hδ := hΩ.rank_prefixCutoff_val P R o κ hs'
  change δ.val = woodinPrefixCutoff P.val R.val o.val κ.val at hδ
  simp only [IsWoodinStage, woodinStagePoset_code, woodinStageOrder_code,
    woodinStageTop_code, woodinStageCardinal_code] at hs'
  let := hs'.2.2.1
  obtain ⟨d, _, hd⟩ := hΩ.strictPrefixCutoff hs'.1 hs'.2.1 P.property R.property
    (ordinal_mem_hierarchy_iff.mp κ.property) hs'.2.2.2.1 hs'.2.2.2.2
  have hδOrd : IsOrdinal δ := (TransitiveZF.ordinal_iff (hierarchy Ω) δ).mpr
    (hδ ▸ (woodinPrefixCutoff_spec hd).1)
  have hiR := (TransitiveZF.forcingPreorder_iff (hierarchy Ω) P R).mpr hs'.1
  have hit := (TransitiveZF.forcingTop_iff (hierarchy Ω) P R o).mpr hs'.2.1
  have hQ := rank_saturatedWoodinPrefixPosetName_val hΩ.inaccessible P R o κ δ hiR hit hδOrd
  change Q.val = saturatedWoodinPrefixPosetName P.val R.val o.val κ.val δ.val at hQ
  have hA : A.val = (forcingCodeP c.val) ‘ k.val := by
    rw [TransitiveZF.value_val_total, TransitiveZF.forcingCodeP_val]
  have hB : B.val = (forcingCodeR c.val) ‘ k.val := by
    rw [TransitiveZF.value_val_total, TransitiveZF.forcingCodeR_val]
  have ht : t.val = (forcingCodet c.val) ‘ k.val := by
    rw [TransitiveZF.value_val_total, TransitiveZF.forcingCodet_val]
  have hf : f.val = m.val ‘ k.val := TransitiveZF.value_val_total _ _ _
  have hmaps : f.val ∈ A.val ^ P.val := by rwa [hf, hA, hP]
  have hpre : IsForcingPreorder A.val B.val := by
    rw [hA, hB]; exact hc.system.order.preorder k.val (mem_succ_self k.val)
  have htop : t.val ∈ A.val := by
    rw [ht, hA]; exact (hc.system.tops.top k.val (mem_succ_self k.val)).1
  have he := TransitiveZF.normalizedTwoStepIsoMap_val_rank Ω P R o δ Q A B t f
    hδOrd hs'.1 hs'.2.1.1 hmaps hpre htop
  simp only [hQ, hδ, hP, hR, ho, hκ, hA, hB, ht, hf] at he
  exact he

theorem IsWoodinSupercompact.rank_woodinSparseSuccessorMap_val {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ k c m : SetDomain (hierarchy Ω), IsOrdinal k →

      IsWoodinStage (woodinIterationStage c.val (kpair.π₂ (woodinIterationRec k.val)) k.val) →
      IsForcingIterationCode (succ k.val) c.val →
      m.val ‘ k.val ∈ ((forcingCodeP c.val) ‘ k.val) ^
        ((forcingCodeP (woodinNormalizedStageCode k.val)) ‘ k.val) →
      (woodinSparseSuccessorMap k c m).val = woodinSparseSuccessorMap k.val c.val m.val := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  intro k c m hk ht hc hm
  let := hk
  let := (TransitiveZF.ordinal_iff (hierarchy Ω) k).mp hk
  have hs := woodinNormalizedStage_isWoodinStage hΩ hAC (ordinal_mem_hierarchy_iff.mp k.property)
  unfold woodinSparseSuccessorMap
  rw [TransitiveZF.compose_val, hΩ.rank_woodinRecodedSuccessorMap_val hAC k c m hk hc hm,
    TransitiveZF.sparsePairEncode_val, TransitiveZF.woodinSourceIndex_val (hierarchy Ω) (succ k) inferInstance,
    TransitiveZF.succ_val, TransitiveZF.value_val_total, TransitiveZF.forcingCodeP_val,
    (hΩ.rank_woodinSparseSuccessor_val hAC k c hk ht).1]

theorem IsWoodinSupercompact.rank_woodinSparseSuccessorMap_actual_val {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ k c m : SetDomain (hierarchy Ω), IsOrdinal k →
      c.val = woodinSparsePrefixCode (succ k.val) →
      m.val = woodinRecodingMaps (woodinSparseRecodingHistory (succ k.val)) →
      (woodinSparseSuccessorMap k c m).val = woodinSparseSuccessorMap k.val c.val m.val := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  intro k c m hk hc hm
  let := hk
  let := (TransitiveZF.ordinal_iff (hierarchy Ω) k).mp hk
  have hkm : k.val ∈ Ω := ordinal_mem_hierarchy_iff.mp k.property
  have hks : k.val ⊆ Ω := IsOrdinal.toIsTransitive.transitive _ hkm
  have hsucc : succ k.val ⊆ Ω := by
    intro i hi
    rcases mem_succ_iff.mp hi with he | hi
    · exact he ▸ hkm
    · exact IsOrdinal.toIsTransitive.mem_trans hi hkm
  have hstage : IsWoodinStage (woodinIterationStage c.val (kpair.π₂ (woodinIterationRec k.val)) k.val) := by
    rw [hc]
    have he : woodinSparsePrefixCode (succ k.val) = woodinSparseStageCode k.val := by
      unfold woodinSparsePrefixCode woodinSparseStageCode
      rw [woodinNormalizedPrefix_successor hΩ hAC hkm]
    rw [he]
    exact woodinSparseStageCode_stage hΩ hAC hks
  have hvalid : IsForcingIterationCode (succ k.val) c.val := hc.symm ▸ woodinSparsePrefixCode_valid hΩ hAC hsucc
  have hmaps : m.val ‘ k.val ∈ ((forcingCodeP c.val) ‘ k.val) ^
      ((forcingCodeP (woodinNormalizedStageCode k.val)) ‘ k.val) := by
    rw [hc, hm]
    have hh := (woodinSparsePrefix_family hΩ hAC hsucc k.val (mem_succ_self k.val)).1
    simpa only [woodinSparsePrefixCode, forcingRecodedCode, forcingCodeP_code,
      woodinNormalizedPrefix_successor hΩ hAC hkm] using hh
  exact hΩ.rank_woodinSparseSuccessorMap_val hAC k c m hk hstage hvalid hmaps
end ZFVP




