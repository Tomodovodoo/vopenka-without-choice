import ZFVP.ModelTheory.WoodinSuccessorBoundTable
import ZFVP.ModelTheory.SuccessorBoundSections
import ZFVP.ModelTheory.WoodinSuccessorUnionBounds
import ZFVP.ModelTheory.WoodinIterationInvariant

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinIteration.successor_bound_table_sectionCompatible {δ k s K B i I : V} [IsOrdinal k]
    (hδ : IsWoodinSupercompact δ) (h : IsWoodinIteration δ (succ k) s K)
    (hi : i ∈ succ k) (hI : I ∈ K ‘ i)
    (hB : IsCoherentForcingBound (succ k) (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s) B i I)
    (hCompatible : IsSectionCompatibleForcingBound (succ k) (forcingCodeP s) (forcingCodeR s)
      (forcingCodeπ s) (forcingCodeE s) B i I) :
    IsSectionCompatibleForcingBound (succ (succ k)) (forcingCodeP (woodinIterationSuccessor k s K))
      (forcingCodeR (woodinIterationSuccessor k s K)) (forcingCodeπ (woodinIterationSuccessor k s K))
      (forcingCodeE (woodinIterationSuccessor k s K)) (woodinSuccessorBoundTable k s K B i I) i I := by
  let := hδ.inaccessible.1
  let x := woodinIterationStage s K k
  have hx : IsWoodinStage x := h.stage k (by simp)
  have hs : IsWoodinStageSmall x := h.small k (by simp)
  have hb : woodinStageCardinal x ∈ δ := by
    simpa [x, woodinIterationStage] using h.bounded k (by simp)
  have hP := hs δ hδ.inaccessible hb
  have hR := hx.order_mem_hierarchy hδ.inaccessible.rankCriterion.2.2.1 hP
  obtain ⟨c, _, hc⟩ := hδ.strictPrefixCutoff hx.1 hx.2.1 hP hR hb hx.2.2.2.1 hx.2.2.2.2
  have hl := (woodinPrefixCutoff_spec hc).2.1
  have hPl := hs _ hl.2.1 hl.1
  have hc' : IsWoodinPrefixCutoff ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k)
      ((forcingCodet s) ‘ k) (K ‘ k)
      (woodinPrefixCutoff ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) ((forcingCodet s) ‘ k) (K ‘ k)) := by
    simpa [x, woodinIterationStage] using hl
  have hstage : IsWoodinStage (woodinStageCode ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k)
      ((forcingCodet s) ‘ k) (K ‘ k)) := hx
  have hreg : ∀ p ∈ (forcingCodeP s) ‘ k, p ∈ forcingFormula ((forcingCodeP s) ‘ k)
      ((forcingCodeR s) ‘ k) regularCardinalFormula (standardTuple ![checkName ((forcingCodet s) ‘ k) (K ‘ k)]) := by
    simpa [x, woodinIterationStage] using hx.2.2.2.1
  have hit := saturatedWoodinPrefix_iterand_of_cutoff (h.code.system.order.preorder k (by simp))
    (h.code.system.tops.top k (by simp)) hreg hc' (by simpa [x, woodinIterationStage] using hPl)
  have hIk : I ∈ K ‘ k := by
    rcases mem_succ_iff.mp hi with he | hik
    · simpa only [he] using hI
    · let := (h.inaccessible k (by simp)).1
      exact IsOrdinal.toIsTransitive.mem_trans hI (h.increasing i hi k (by simp) hik)
  have hmax : ∀ j ∈ succ k, j ⊆ k := by
    intro j hj
    rcases mem_succ_iff.mp hj with rfl | hj
    · exact subset_refl _
    · exact IsOrdinal.toIsTransitive.transitive _ hj
  have hcB := successor_coherentBoundColumn h.code.system.split h.code.system.functions hB hi
    (mem_succ_self k) hmax (h.code.system.order.preorder k (by simp)) (h.code.system.tops.top k (by simp)) hit
    (fun f hf q hq hqb ↦ by
      simpa only [woodinSuccessorAt, woodinStagePoset_code, woodinStageOrder_code] using
        woodinSuccessorAt_union_bound hstage hc' hq hIk
          (by simpa only [woodinSuccessorAt, woodinStagePoset_code, woodinStageOrder_code] using hf) hqb)
  have hsB := successor_sectionCompatibleBoundColumn h.code.system.split h.code.system.functions hB hCompatible
    (mem_succ_self k) hmax (h.code.system.order.preorder k (by simp)) (h.code.system.tops.top k (by simp)) hit
  have he := hCompatible.extend hcB hsB hi
  simpa only [woodinIterationSuccessor, forcingSuccessorCode, forcingIterationCodeNext,
    forcingCodeP_code, forcingCodeR_code, forcingCodeπ_code, forcingCodeE_code, woodinSuccessorBoundTable] using he

end ZFVP
