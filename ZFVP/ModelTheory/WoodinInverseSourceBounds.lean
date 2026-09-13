import ZFVP.ModelTheory.WoodinInverseIteration
import ZFVP.ModelTheory.InverseSourceCollapseBounds
import ZFVP.SetTheory.ChoicelessInaccessibleRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinInverseSourceBoundTable (θ s K B i I : V) : V :=
  forcingInverseSourceCollapseBoundTable θ s (forcingInverseSourceCutoff θ s (woodinLimitCardinal K))
    (woodinLimitCardinal K) B i I

theorem IsWoodinIteration.inverse_source_bound_table {δ θ s K B i I : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (hδ : IsWoodinSupercompact δ) (hθ : θ ∈ δ) (h0 : ∅ ∈ θ)
    (hi : i ∈ θ) (hI : I ∈ K ‘ i)
    (hγ : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        (regularCardinalFormula.or limitOfRegularCardinalsFormula)
        (standardTuple ![checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K)]))
    (hDC : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        dependentChoiceAtFormula (standardTuple ![checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K)]))
    (hb : IsCoherentForcingBound θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s) B i I)
    (hc : IsSectionCompatibleForcingBound θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s)
      (forcingCodeE s) B i I) :
    let z := woodinInverseSourceCode θ s K
    let B' := woodinInverseSourceBoundTable θ s K B i I
    IsCoherentForcingBound (succ θ) (forcingCodeP z) (forcingCodeR z) (forcingCodeπ z) B' i I ∧
      IsSectionCompatibleForcingBound (succ θ) (forcingCodeP z) (forcingCodeR z) (forcingCodeπ z)
        (forcingCodeE z) B' i I := by
  obtain ⟨_, hcut⟩ := h.inverse_sourceCutoff hδ hθ h0 hγ hDC
  let := h.limitCardinal_ordinal
  have hIγ := h.cardinal_subset_limit hi I hI
  have hIc : I ∈ internalCofinality (forcingInverseSourceCutoff θ s (woodinLimitCardinal K)) := by
    rw [hcut.2.1.cofinality]
    exact IsOrdinal.toIsTransitive.mem_trans hIγ hcut.1
  have hz : (∅ : V) ∈ forcingNameHierarchy (forcingInverseCodePoset θ s)
      (forcingInverseSourceCutoff θ s (woodinLimitCardinal K)) :=
    (mem_forcingNameHierarchy _ _ _).mpr ⟨∅, hcut.2.1.regular.2.1 ∅ (by simp), by simp⟩
  exact forcingInverseSourceCollapseCode_bound_table h.code h0 hi hz hIc hIγ hγ hDC hb hc

end ZFVP

