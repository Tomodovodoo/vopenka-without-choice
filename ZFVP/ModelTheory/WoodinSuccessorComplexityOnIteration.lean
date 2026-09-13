import ZFVP.ModelTheory.SigmaThreeWoodinCardinalNext
import ZFVP.ModelTheory.WoodinIterationInvariant

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

theorem woodinSuccessorStage_deltaThree_on_iteration :
    ∃ σ π σc πc : SetTheorySemisentence 4,
      IsSigmaFormula 3 σ ∧ IsPiFormula 3 π ∧ IsSigmaFormula 3 σc ∧ IsPiFormula 3 πc ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙], ∀ δ k s K : V,
        IsOrdinal k → IsWoodinSupercompact δ → IsWoodinIteration δ (succ k) s K → ∀ z,
          (σ.Evalb ![z, k, s, K] ↔ z = woodinIterationSuccessor k s K) ∧
          (π.Evalb ![z, k, s, K] ↔ z = woodinIterationSuccessor k s K) ∧
          (σc.Evalb ![z, k, s, K] ↔ z = woodinIterationCardinalNext k s K) ∧
          (πc.Evalb ![z, k, s, K] ↔ z = woodinIterationCardinalNext k s K) := by
  obtain ⟨σ, π, hσ, hπ, hcode⟩ := woodinIterationSuccessor_deltaThree_uniform.{u}
  obtain ⟨σc, πc, hσc, hπc, hcard⟩ := woodinIterationCardinalNext_deltaThree_uniform.{u}
  refine ⟨σ, π, σc, πc, hσ, hπ, hσc, hπc, ?_⟩
  intro V _ _ _ δ k s K hk hδ h z
  let := hk
  let := hδ.inaccessible.1
  let x := woodinIterationStage s K k
  have hx : IsWoodinStage x := h.stage k (by simp)
  have hs : IsWoodinStageSmall x := h.small k (by simp)
  have hb : woodinStageCardinal x ∈ δ := by
    simpa [x, woodinIterationStage] using h.bounded k (by simp)
  have hP := hs δ hδ.inaccessible hb
  have hR := hx.order_mem_hierarchy hδ.inaccessible.rankCriterion.2.2.1 hP
  obtain ⟨c, _, hc⟩ := hδ.strictPrefixCutoff hx.1 hx.2.1 hP hR hb hx.2.2.2.1 hx.2.2.2.2
  have hc' : IsWoodinPrefixCutoff ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k)
      ((forcingCodet s) ‘ k) (K ‘ k) c := by
    simpa [x, woodinIterationStage] using hc
  have hl := (woodinPrefixCutoff_spec hc).2.1
  have hPl : (forcingCodeP s) ‘ k ∈ hierarchy
      (woodinPrefixCutoff ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) ((forcingCodet s) ‘ k) (K ‘ k)) := by
    simpa [x, woodinIterationStage] using hs _ hl.2.1 hl.1
  have hz : (∅ : V) ∈ K ‘ k := (h.inaccessible k (by simp)).regular.2.1 ∅ (by simp)
  have hp := h.code.system.order.preorder k (by simp)
  have ht := h.code.system.tops.top k (by simp)
  have hreg : ∀ p ∈ (forcingCodeP s) ‘ k, p ∈ forcingFormula
      ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) regularCardinalFormula
      (standardTuple ![checkName ((forcingCodet s) ‘ k) (K ‘ k)]) := by
    simpa [x, woodinIterationStage] using hx.2.2.2.1
  have hC := hcode V k s K hp ht hz hreg ⟨c, hc'⟩ hPl z
  have hK := hcard V k s K hp ht hz ⟨c, hc'⟩ z
  exact ⟨hC.1, hC.2, hK.1, hK.2⟩

end ZFVP
