import ZFVP.ModelTheory.WoodinRankStage
import ZFVP.ModelTheory.SaturatedWoodinRankSuccessor
import ZFVP.ModelTheory.WoodinLimitCardinals

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The actual selected successor advances the rank invariant. -/
theorem IsWoodinIteration.successor_rankEnumerations [Countable V] {δ k s K : V} [IsOrdinal k]
    (hδ : IsWoodinSupercompact δ) (h : IsWoodinIteration δ (succ k) s K)
    (henum : WoodinRankStage k s K) :
    WoodinRankStage (succ k) (woodinIterationSuccessor k s K) (woodinIterationCardinalNext k s K) := by
  let x := woodinIterationStage s K k
  have hx : IsWoodinStage x := h.stage k (mem_succ_self k)
  have hs : IsWoodinStageSmall x := h.small k (mem_succ_self k)
  have hb : woodinStageCardinal x ∈ δ := by
    simpa [x, woodinIterationStage] using h.bounded k (mem_succ_self k)
  let := hδ.inaccessible.1
  have hP := hs δ hδ.inaccessible hb
  have hR := hx.order_mem_hierarchy hδ.inaccessible.rankCriterion.2.2.1 hP
  obtain ⟨c, _, hc⟩ := hδ.strictPrefixCutoff hx.1 hx.2.1 hP hR hb hx.2.2.2.1 hx.2.2.2.2
  have hl := (woodinPrefixCutoff_spec hc).2.1
  have hPl := hs _ hl.2.1 hl.1
  let := (h.inaccessible k (mem_succ_self k)).1
  have hkcut : k ∈ woodinPrefixCutoff (woodinStagePoset x) (woodinStageOrder x)
      (woodinStageTop x) (woodinStageCardinal x) := by
    let := hl.2.1.1
    apply ordinal_mem_of_subset_mem (h.index_subset_cardinal k (mem_succ_self k))
    simpa only [x, woodinIterationStage, woodinStageCardinal_code] using hl.1
  have hen : ∀ p ∈ woodinStagePoset x, p ∈ forcingFormula (woodinStagePoset x) (woodinStageOrder x)
    shortRankEnumerationsFormula
      (standardTuple ![checkName (woodinStageTop x) k, checkName (woodinStageTop x) (woodinStageCardinal x)]) := by
    simpa only [x, woodinIterationStage, woodinStagePoset_code, woodinStageOrder_code,
      woodinStageTop_code, woodinStageCardinal_code, WoodinRankStage, ForcesRankEnumerations] using henum
  have hh := saturatedWoodinSuccessor_forces_rankEnumerations hx.1 hx.2.1 hx.2.2.2.1 hl hPl
    hkcut hx.2.2.2.2 hen
  simpa only [WoodinRankStage, ForcesRankEnumerations, woodinIterationSuccessor,
    forcingSuccessorCode, forcingIterationCodeNext, forcingCodeP_code, forcingCodeR_code,
    forcingCodet_code, woodinIterationCardinalNext, forcingFamilyNext_new,
    x, woodinIterationStage, woodinSuccessorStep, woodinSuccessorAt, woodinStagePoset_code, woodinStageOrder_code,
    woodinStageTop_code, woodinStageCardinal_code] using hh

end ZFVP
