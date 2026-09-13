import ZFVP.ModelTheory.WoodinQuotientClosureDirect
import ZFVP.ModelTheory.DirectLimitStageTransfer
import ZFVP.ModelTheory.WoodinLimitBase

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinIteration.direct_of_limit_below {δ θ s K : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (hc : HasWoodinQuotientClosure θ s K)
    (hbound : woodinLimitCardinal K ∈ δ) (h0 : ∅ ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal K)) :
    IsWoodinIteration δ (succ θ) (forcingDirectCode θ s)
      (forcingFamilyNext θ K (woodinLimitCardinal K)) := by
  let z := forcingDirectCode θ s
  let L := forcingFamilyNext θ K (woodinLimitCardinal K)
  have hz : IsForcingIterationCode (succ θ) z := forcingDirectCode_valid h.code h0
  have he := h.index_eq_regular_limit hlim hinac.regular
  have hθ : IsChoicelessInaccessible θ := he.symm ▸ hinac
  have hKi (i : V) (hi : i ∈ θ) : K ‘ i ∈ θ := he.symm ▸ h.cardinal_mem_limit hlim hi
  have hs (i : V) (hi : i ∈ θ) : (forcingCodeP s) ‘ i ∈ hierarchy θ := by
    have hh := h.small i hi θ hθ
    simp only [woodinIterationStage, woodinStagePoset_code, woodinStageCardinal_code] at hh
    exact hh (hKi i hi)
  have hcof : ∀ β ∈ θ, ∃ i ∈ θ, β ∈ K ‘ i := by
    intro β hβ
    exact h.limitCardinal_cofinal (he ▸ hβ)
  have hDC : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP s) ‘ i, p ∈ forcingFormula
      ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i) dependentChoiceBelowFormula
      (standardTuple ![checkName ((forcingCodet s) ‘ i) (K ‘ i)]) := by
    intro i hi
    simpa only [woodinIterationStage, woodinStagePoset_code, woodinStageOrder_code,
      woodinStageTop_code, woodinStageCardinal_code] using (h.stage i hi).2.2.2.2
  have hf := directLimit_stage_forced hθ h.code.system.split h.code.system.order.preorder h.code.system.tops.top
    (fun i hi j hj hij ↦ h.code.system.splitProjection hi hj hij) h.code.subset_universe hs hKi hcof hDC hc
    (show (forcingCodeP z) ‘ θ = forcingDirectLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s) (forcingCodeUniverse s) by
      simp only [z, forcingDirectCode, forcingThreadCode_poset])
    (show (forcingCodeR z) ‘ θ = forcingThreadOrder θ (forcingCodeR s) ((forcingCodeP z) ‘ θ) by
      simp only [z, forcingDirectCode, forcingThreadCode_poset, forcingThreadCode_order])
    (hz.system.tops.top θ (mem_succ_self θ))
  have hf' : ∀ p ∈ (forcingCodeP z) ‘ θ, p ∈ forcingFormula ((forcingCodeP z) ‘ θ) ((forcingCodeR z) ‘ θ)
      woodinStageCardinalFormula (standardTuple ![checkName ((forcingCodet z) ‘ θ) (woodinLimitCardinal K)]) := by
    simpa only [← he, directStageCardinalFormula, woodinStageCardinalFormula] using hf
  have hold (i : V) (hi : i ∈ θ) : L ‘ i = K ‘ i := forcingFamilyNext_old hi
  have hnew : L ‘ θ = woodinLimitCardinal K := forcingFamilyNext_new _ _ _
  have hstageold (i : V) (hi : i ∈ θ) : woodinIterationStage z L i = woodinIterationStage s K i := by
    simp only [woodinIterationStage, z, forcingDirectCode, forcingThreadCode, forcingIterationCodeNext,
      forcingCodeP_code, forcingCodeR_code, forcingCodet_code, forcingFamilyNext_old hi, hold i hi]
  refine ⟨hz, forcingFamilyNext_table _ _ _, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rcases mem_succ_iff.mp hi with hEq | hi
    · subst i
      simp only [IsWoodinStage, woodinIterationStage, woodinStagePoset_code, woodinStageOrder_code,
        woodinStageTop_code, woodinStageCardinal_code, forcingFamilyNext_new]
      refine ⟨hz.system.order.preorder θ (mem_succ_self θ), hz.system.tops.top θ (mem_succ_self θ), hinac.1, ?_, ?_⟩
      · intro p hp
        have hh := hf' p hp
        rw [woodinStageCardinalFormula, forcingFormula_and, mem_inter_iff] at hh
        exact hh.1
      · intro p hp
        have hh := hf' p hp
        rw [woodinStageCardinalFormula, forcingFormula_and, mem_inter_iff] at hh
        exact hh.2
    · rw [hstageold i hi]
      exact h.stage i hi
  · intro i hi
    rcases mem_succ_iff.mp hi with hEq | hi
    · subst i
      intro ε hε hγε
      simp only [woodinIterationStage, woodinStageCardinal_code, forcingFamilyNext_new] at hγε
      have hb := (h.limitBase_small hlim hε hγε).1
      rw [woodinLimitBase_direct hinac] at hb
      simpa only [woodinIterationStage, woodinStagePoset_code] using hb
    · rw [hstageold i hi]
      exact h.small i hi
  · intro i hi
    rcases mem_succ_iff.mp hi with hEq | hi
    · subst i
      exact hnew.symm ▸ hinac
    · rw [hold i hi]
      exact h.inaccessible i hi
  · intro i hi
    rcases mem_succ_iff.mp hi with hEq | hi
    · subst i
      rw [hnew]
      exact hbound
    · rw [hold i hi]
      exact h.bounded i hi
  · intro i hi j hj hij
    rcases mem_succ_iff.mp hj with hEq | hj
    · subst j
      rw [hold i hij, hnew]
      exact h.cardinal_mem_limit hlim hij
    · have hiold : i ∈ θ := IsOrdinal.toIsTransitive.mem_trans hij hj
      rw [hold i hiold, hold j hj]
      exact h.increasing i hiold j hj hij

theorem IsWoodinIteration.direct {δ θ s K : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (hc : HasWoodinQuotientClosure θ s K)
    (hδ : IsRegularCardinal δ) (hθδ : θ ∈ δ) (h0 : ∅ ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal K)) :
    IsWoodinIteration δ (succ θ) (forcingDirectCode θ s)
      (forcingFamilyNext θ K (woodinLimitCardinal K)) :=
  h.direct_of_limit_below hc (h.limitCardinal_below hδ hθδ) h0 hlim hinac

end ZFVP
