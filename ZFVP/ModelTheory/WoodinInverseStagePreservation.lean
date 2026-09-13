import ZFVP.ModelTheory.WoodinLimitSingular
import ZFVP.ModelTheory.SingularLimitStageTransfer
import ZFVP.ModelTheory.WoodinInverseIteration
import ZFVP.ModelTheory.IterationQuotientClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinIteration.inverse_stage_forced_of_quotient_closure {δ θ s K : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (h0 : ∅ ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal K))
    (hc : ∀ i ∈ θ, IterationQuotientClosedBelow (forcingInverseCode θ s) i θ (K ‘ i)) :
    ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        singularLimitStageFormula (standardTuple ![checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K)]) := by
  let := h.limitCardinal_ordinal
  let z := forcingInverseCode θ s
  have hz : IsForcingIterationCode (succ θ) z := forcingInverseCode_valid h.code h0
  let π := definableGraph θ (fun i ↦ (forcingCodeπ z) ‘ ⟨i, θ⟩ₖ) (by definability)
  let E := definableGraph θ (fun i ↦ (forcingCodeE z) ‘ ⟨i, θ⟩ₖ) (by definability)
  have hπ (i : V) (hi : i ∈ θ) : π ‘ i = (forcingCodeπ z) ‘ ⟨i, θ⟩ₖ :=
    value_definableGraph _ _ _ hi
  have hE (i : V) (hi : i ∈ θ) : E ‘ i = (forcingCodeE z) ‘ ⟨i, θ⟩ₖ :=
    value_definableGraph _ _ _ hi
  have hi' (i : V) (hi : i ∈ θ) : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
  have hstage (i : V) (hi : i ∈ θ) : ∀ p ∈ (forcingCodeP z) ‘ i,
      p ∈ forcingFormula ((forcingCodeP z) ‘ i) ((forcingCodeR z) ‘ i) woodinStageCardinalFormula
        (standardTuple ![checkName ((forcingCodet z) ‘ i) (K ‘ i)]) := by
    simp only [z, forcingInverseCode, forcingThreadCode, forcingIterationCodeNext,
      forcingCodeP_code, forcingCodeR_code, forcingCodet_code, forcingFamilyNext_old hi]
    intro p hp
    rw [woodinStageCardinalFormula, forcingFormula_and, mem_inter_iff]
    have hs := h.stage i hi
    simp only [IsWoodinStage, woodinIterationStage, woodinStagePoset_code, woodinStageOrder_code,
      woodinStageTop_code, woodinStageCardinal_code] at hs
    exact ⟨hs.2.2.2.1 p hp, hs.2.2.2.2 p hp⟩
  have hh := singularLimit_stage_forced (P := forcingCodeP z) (R := forcingCodeR z)
    (t := forcingCodet z) (K := K) (π := π) (E := E)
    (IsOrdinal.toIsTransitive.transitive _ (h.limitCardinal_omega_mem h0))
    h.limitCardinal_succ_closed (h.limitCardinal_singular h0 hlim hn)
    (fun i hi ↦ h.cardinal_mem_limit hlim hi) (fun _ ha ↦ h.limitCardinal_cofinal ha)
    (fun i hi ↦ hz.system.order.preorder i (hi' i hi))
    (fun i hi ↦ hz.system.tops.top i (hi' i hi))
    (fun i hi ↦ by
      rw [hπ i hi, hE i hi]
      exact hz.system.splitProjection (hi' i hi) (mem_succ_self θ)
        (IsOrdinal.toIsTransitive.transitive _ hi)) hstage
    (fun i hi ↦ by rw [hπ i hi]; exact hc i hi)
    (hz.system.order.preorder θ (mem_succ_self θ)) (hz.system.tops.top θ (mem_succ_self θ))
  simpa only [z, forcingInverseCode, forcingThreadCode_poset, forcingThreadCode_order,
    forcingThreadCode_top, forcingInverseCodePoset, forcingInverseCodeOrder, forcingInverseCodeTop] using hh

/-- All preservation hypotheses of the source inverse extension now follow
from the final inverse quotients' closure. That closure remains a separate obligation. -/
theorem IsWoodinIteration.inverse_source_of_quotient_closure {δ θ s K : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (hδ : IsWoodinSupercompact δ) (hθ : θ ∈ δ)
    (h0 : ∅ ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal K))
    (hc : ∀ i ∈ θ, IterationQuotientClosedBelow (forcingInverseCode θ s) i θ (K ‘ i)) :
    IsWoodinIteration δ (succ θ) (woodinInverseSourceCode θ s K) (woodinInverseCardinalNext θ s K) := by
  have hf := h.inverse_stage_forced_of_quotient_closure h0 hlim hn hc
  have c := h.code.system.inverseColumn h0 h.code.subset_universe
  have hR : IsForcingPreorder (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s) := c.order.preorder
  have ht : IsForcingTop (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseCodeTop θ s) := c.tops.top
  let τ : ForcingName (forcingInverseCodePoset θ s) :=
    ⟨checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K), checkName_isName ht.1 _⟩
  apply h.inverse_source hδ hθ h0 hlim
  · intro p hp
    apply forcingFormula_entailment singularLimitStageFormula
      (regularCardinalFormula.or limitOfRegularCardinalsFormula) ?_ hR ht hp ![τ] (hf p hp)
    intro W _ _ _ v hv
    have hh : IsLimitOfRegularCardinals (v 0) ∧ InternalDependentChoiceAt (v 0) :=
      (Defined.eval_iff _).mp hv
    change regularCardinalFormula.Evalb v ∨ limitOfRegularCardinalsFormula.Evalb v
    exact Or.inr ((Defined.eval_iff _).mpr hh.1)
  · intro p hp
    have hh := hf p hp
    rw [singularLimitStageFormula, forcingFormula_and, mem_inter_iff] at hh
    exact hh.2

end ZFVP
