import ZFVP.ModelTheory.ForcingLimitCode
import ZFVP.ModelTheory.WoodinLimitCardinals

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The limit forcing before the additional collapse in the noninaccessible branch. -/
noncomputable def woodinLimitBase (θ s K : V) : V := by
  classical
  exact if IsChoicelessInaccessible (woodinLimitCardinal K)
    then forcingDirectCode θ s else forcingInverseCode θ s

theorem woodinLimitBase_direct {θ s K : V}
    (h : IsChoicelessInaccessible (woodinLimitCardinal K)) :
    woodinLimitBase θ s K = forcingDirectCode θ s := by simp [woodinLimitBase, h]

theorem woodinLimitBase_inverse {θ s K : V}
    (h : ¬IsChoicelessInaccessible (woodinLimitCardinal K)) :
    woodinLimitBase θ s K = forcingInverseCode θ s := by simp [woodinLimitBase, h]

theorem woodinLimitBase_valid {θ s K : V} [IsOrdinal θ]
    (h : IsForcingIterationCode θ s) (h0 : ∅ ∈ θ) :
    IsForcingIterationCode (succ θ) (woodinLimitBase θ s K) := by
  classical
  by_cases hc : IsChoicelessInaccessible (woodinLimitCardinal K)
  · rw [woodinLimitBase_direct hc]
    exact forcingDirectCode_valid h h0
  · rw [woodinLimitBase_inverse hc]
    exact forcingInverseCode_valid h h0

theorem woodinLimitBase_extends {θ s : V} (h : IsForcingIterationCode θ s) (K : V) :
    ForcingCodeExtends s (woodinLimitBase θ s K) := by
  classical
  by_cases hc : IsChoicelessInaccessible (woodinLimitCardinal K)
  · rw [woodinLimitBase_direct hc]
    exact forcingThreadCode_extends h _
  · rw [woodinLimitBase_inverse hc]
    exact forcingThreadCode_extends h _

theorem IsWoodinIteration.limitBase_small {δ θ s K ε : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hε : IsChoicelessInaccessible ε) (hγε : woodinLimitCardinal K ∈ ε) :
    (forcingCodeP (woodinLimitBase θ s K)) ‘ θ ∈ hierarchy ε ∧
      (forcingCodeR (woodinLimitBase θ s K)) ‘ θ ∈ hierarchy ε := by
  classical
  let := hε.1
  have : IsOrdinal (woodinLimitCardinal K) := h.limitCardinal_ordinal
  have hθε := ordinal_mem_of_subset_mem (h.index_subset_limit hlim) hγε
  have hθ : θ ∈ hierarchy ε := ordinal_mem_hierarchy_iff.mpr hθε
  have hP : forcingCodeP s ∈ hierarchy ε ^ θ := by
    apply h.code.tableP.mem_function
    intro i hi
    have hκ : K ‘ i ∈ ε := IsOrdinal.toIsTransitive.mem_trans (h.cardinal_mem_limit hlim hi) hγε
    have hb : woodinStageCardinal (woodinIterationStage s K i) ∈ ε := by
      simpa [woodinIterationStage] using hκ
    simpa [woodinIterationStage] using h.small i hi ε hε hb
  by_cases hc : IsChoicelessInaccessible (woodinLimitCardinal K)
  · rw [woodinLimitBase_direct hc]
    simp only [forcingDirectCode, forcingThreadCode_poset, forcingThreadCode_order, forcingCodeUniverse]
    exact forcingDirectLimit_small_family hε hθ hP
  · rw [woodinLimitBase_inverse hc]
    simp only [forcingInverseCode, forcingThreadCode_poset, forcingThreadCode_order, forcingCodeUniverse]
    exact forcingInverseLimit_small_family hε hθ hP

end ZFVP
