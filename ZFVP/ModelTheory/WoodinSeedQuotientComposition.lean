import ZFVP.ModelTheory.WoodinSourceSeedQuotientClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSourceCode_seed_positive_quotient_of_first {θ s K j : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (hQ : HasWoodinQuotientClosure θ s K)
    (h0 : (∅ : V) ∈ θ) (hj : j ∈ θ) (hμ : woodinSeedCardinal ⊆ K ‘ ∅)
    (hbase : IterationQuotientClosedBelow (woodinSourceCode θ s) ∅ (woodinSourceIndex ∅) woodinSeedCardinal) :
    IterationQuotientClosedBelow (woodinSourceCode θ s) ∅ (woodinSourceIndex j) woodinSeedCardinal := by
  let := IsOrdinal.of_mem hj
  have hs' := woodinSourceCode_valid hs
  have hz : (∅ : V) ∈ woodinSourceIndex θ :=
    subset_ordinalAdd 1 θ ∅ (by change (0 : V) ∈ succ 0; simp)
  have hi := woodinSourceIndex_mem_iff.mpr h0
  have hj' := woodinSourceIndex_mem_iff.mpr hj
  have hij : woodinSourceIndex (∅ : V) ⊆ woodinSourceIndex j := ordinalAdd_mono_right 1 (empty_subset j)
  have htail := woodinSourceCode_positive_quotient hQ h0 hj (empty_subset j)
  rw [woodinSourceCardinals_stage h0] at htail
  have htail' := projectionQuotient_closedBelow_mono_forced
    (hs'.system.order.preorder _ hi) (hs'.system.tops.top _ hi)
    (hs'.system.order.preorder _ hj') (hs'.system.projection hi hj' hij) hμ htail
  exact projectionQuotient_closedBelow_comp_forced
    (hs'.system.order.preorder _ hz) (hs'.system.tops.top _ hz)
    (hs'.system.splitProjection hz hi (empty_subset _))
    (hs'.system.order.preorder _ hi) (hs'.system.tops.top _ hi)
    (hs'.system.order.preorder _ hj') (hs'.system.projection hz hj' (empty_subset _))
    (hs'.system.projection hi hj' hij)
    (hs'.system.split.projComp _ hz _ hi _ hj' (empty_subset _) hij) hbase htail'

theorem woodinSourceCode_quotient_closure_of_seed {θ s K : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (hQ : HasWoodinQuotientClosure θ s K)
    (h0 : (∅ : V) ∈ θ) (hμ : woodinSeedCardinal ⊆ K ‘ ∅)
    (hbase : IterationQuotientClosedBelow (woodinSourceCode θ s) ∅ (woodinSourceIndex ∅) woodinSeedCardinal) :
    HasWoodinQuotientClosure (woodinSourceIndex θ) (woodinSourceCode θ s) (woodinSourceCardinals θ K) := by
  intro i hi j hj hij
  rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
  · rw [woodinSourceCardinals_seed]
    rcases woodinSourceIndex_cases hj with rfl | ⟨b, hb, rfl⟩
    · exact (woodinSourceCode_valid hs).diagonal_quotient_closedBelow hi _
    · exact woodinSourceCode_seed_positive_quotient_of_first hs hQ h0 hb hμ hbase
  · let := IsOrdinal.of_mem ha
    rcases woodinSourceIndex_cases hj with rfl | ⟨b, hb, rfl⟩
    · have he : woodinSourceIndex a = ∅ := SetTheory.subset_antisymm hij (empty_subset _)
      exact False.elim (woodinSourceIndex_nonzero a he)
    · let := IsOrdinal.of_mem hb
      apply woodinSourceCode_positive_quotient hQ ha hb
      rcases IsOrdinal.subset_iff.mp hij with he | hm
      · exact IsOrdinal.subset_iff.mpr (Or.inl (woodinSourceIndex_injective he))
      · exact IsOrdinal.toIsTransitive.transitive _ (woodinSourceIndex_mem_iff.mp hm)

end ZFVP
