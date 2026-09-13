import ZFVP.ModelTheory.ForcingLimitBoundTables
import ZFVP.ModelTheory.WoodinLimitBase

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinLimitBaseBoundTable (θ s K B i I : V) : V := by
  classical
  exact if IsChoicelessInaccessible (woodinLimitCardinal K)
    then forcingDirectBoundTable θ s B i I else forcingInverseBoundTable θ s B i I

theorem IsWoodinIteration.limitBase_bound_table {δ θ s K B i I : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (hlim : ∀ j ∈ θ, succ j ∈ θ)
    (hi : i ∈ θ) (hI : I ∈ K ‘ i)
    (hB : IsCoherentForcingBound θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s) B i I)
    (hc : IsSectionCompatibleForcingBound θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s)
      (forcingCodeE s) B i I) :
    IsCoherentForcingBound (succ θ) (forcingCodeP (woodinLimitBase θ s K))
      (forcingCodeR (woodinLimitBase θ s K)) (forcingCodeπ (woodinLimitBase θ s K))
      (woodinLimitBaseBoundTable θ s K B i I) i I ∧
    IsSectionCompatibleForcingBound (succ θ) (forcingCodeP (woodinLimitBase θ s K))
      (forcingCodeR (woodinLimitBase θ s K)) (forcingCodeπ (woodinLimitBase θ s K))
      (forcingCodeE (woodinLimitBase θ s K)) (woodinLimitBaseBoundTable θ s K B i I) i I := by
  classical
  by_cases hinac : IsChoicelessInaccessible (woodinLimitCardinal K)
  · simp only [woodinLimitBase, woodinLimitBaseBoundTable, ite_eq_left hinac]
    have hcof := h.short_below_direct_cofinality hlim hinac hi hI
    exact ⟨h.code.direct_bound_table hi hcof hB hc,
      h.code.direct_bound_table_sectionCompatible hi hcof hB hc⟩
  · simp only [woodinLimitBase, woodinLimitBaseBoundTable, ite_eq_right hinac]
    exact ⟨h.code.inverse_bound_table hi hB,
      h.code.inverse_bound_table_sectionCompatible hi hB hc⟩

end ZFVP
