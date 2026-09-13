import ZFVP.SetTheory.WeaklyLSNoSmallSurjection
import ZFVP.SetTheory.SmallSurjectionProduct
import ZFVP.SetTheory.Cofinality
import ZFVP.SetTheory.SmallCollapseUnionSurjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Canonically enumerate the range of a cofinal map by its ordinal order type. -/
theorem IsCofinalMap.orderType_range_cofinal {α x f : V} [IsOrdinal α]
    (hf : IsCofinalMap α x f) :
    IsCofinalMap α (internalOrderType (membershipRelation (range f)) (range f))
      (converseGraph (mostowskiMap (membershipRelation (range f)) (range f))) := by
  have hw := ordinalSubset_membership_wellOrder (range_subset_of_mem_function hf.1)
  have hc := mostowskiMap_isTransitiveCollapse hw.2.1 (internalWellOrder_extensional hw)
  have hinv := converseGraph_mem_function hc.2.1 hc.injective
  refine ⟨mem_function_of_mem_function_of_subset hinv (range_subset_of_mem_function hf.1), ?_⟩
  intro ξ hξ
  obtain ⟨i, hi, hξi⟩ := hf.2 ξ hξ
  have hfi : f ‘ i ∈ range f := value_mem_range hf.1 hi
  refine ⟨(mostowskiMap (membershipRelation (range f)) (range f)) ‘ (f ‘ i),
    function_value_mem hc.2.1 hfi, ?_⟩
  rw [converseGraph_value_value hc.2.1 hc.injective hfi]
  exact hξi

/-- The cofinality of an ordinal does not exceed the order type of the range
of any cofinal map into it, even when the original domain is not well-orderable. -/
theorem IsCofinalMap.cofinality_subset_orderType_range {α x f : V} [IsOrdinal α]
    (hf : IsCofinalMap α x f) :
    internalCofinality α ⊆ internalOrderType (membershipRelation (range f)) (range f) := by
  have := internalOrderType_ordinal
    (ordinalSubset_membership_wellOrder (range_subset_of_mem_function hf.1))
  exact internalCofinality_minimal hf.orderType_range_cofinal

/-- Sets below a weakly LS cardinal cannot be cofinal in an ordinal of
cofinality at least that cardinal. -/
theorem IsWeaklyLSCardinal.no_small_cofinalMap_of_cofinality {ν α x f : V}
    [IsOrdinal α] (hν : IsWeaklyLSCardinal ν) (hx : x ∈ hierarchy ν)
    (hνcf : ν ⊆ internalCofinality α) : ¬IsCofinalMap α x f := by
  intro hf
  have : IsOrdinal ν := hν.1.1
  have htype := orderType_range_lt_of_no_surjection (show IsNonempty ν from ⟨ω, hν.2.1⟩)
    (fun g hg ↦ hν.no_small_surjection hx hg) hf.1
  exact mem_irrefl _ (hf.cofinality_subset_orderType_range _ (hνcf _ htype))

end ZFVP
