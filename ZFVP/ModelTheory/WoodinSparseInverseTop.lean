import ZFVP.ModelTheory.WoodinSparseInverseBase
import ZFVP.ModelTheory.ForcingRecodedExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {θ c : V} [IsOrdinal θ]

private theorem sparseThreadOrder_subset' (θ b R C : V) : sparseThreadOrder θ b R C ⊆ C ×ˢ C := sep_subset

theorem woodinSparseInverseFlatten_top
    (hc : IsForcingIterationCode θ c) (h0 : ∅ ∈ θ)
    (hsp : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p)
    (hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
      ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)))
    (ht : ∀ i ∈ θ, (forcingCodet c) ‘ i = ∅) :
    (woodinSparseInverseFlatten θ c) ‘ (forcingInverseCodeTop θ c) = ∅ := by
  have htop : forcingInverseCodeTop θ c ∈ forcingInverseCodePoset θ c :=
    (hc.system.inverseColumn h0 hc.subset_universe).tops.top.1
  have hthreads := htop
  rw [woodinSparseInverse_threads hsp hπ] at hthreads
  rw [woodinSparseInverseFlatten_value hsp hπ htop]
  apply subset_empty_iff_eq_empty.mp
  intro z hz
  obtain ⟨p, hp, hz⟩ := mem_sUnion_iff.mp hz
  obtain ⟨i, hi, he⟩ := sparseRestrictionThread_range hthreads hp
  have hi0 : (forcingInverseCodeTop θ c) ‘ i = ∅ :=
    (forcingSectionThread_top_value hc.system.tops h0 hi).trans (ht i hi)
  exact (he.symm.trans hi0) ▸ hz

theorem woodinSparseInverse_preorder
    (hc : IsForcingIterationCode θ c) (h0 : ∅ ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hsp : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p)
    (hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
      ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i))) :
    IsForcingPreorder (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c) :=
  (woodinSparseInverseFlatten_isomorphism hc h0 hlim hsp hπ).target_preorder
    (hc.system.inverseColumn h0 hc.subset_universe).order.preorder (sparseThreadOrder_subset' _ _ _ _)

theorem woodinSparseInverse_empty_top
    (hc : IsForcingIterationCode θ c) (h0 : ∅ ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hsp : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p)
    (hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
      ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)))
    (ht : ∀ i ∈ θ, (forcingCodet c) ‘ i = ∅) :
    IsForcingTop (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c) ∅ := by
  have hf := woodinSparseInverseFlatten_isomorphism hc h0 hlim hsp hπ
  have htop : IsForcingTop (forcingInverseCodePoset θ c) (forcingInverseCodeOrder θ c)
      (forcingInverseCodeTop θ c) := (hc.system.inverseColumn h0 hc.subset_universe).tops.top
  have he := woodinSparseInverseFlatten_top hc h0 hsp hπ ht
  refine ⟨he ▸ function_value_mem hf.1 htop.1, ?_⟩
  intro q hq
  obtain ⟨p, hp, rfl⟩ := hf.surjective q hq
  rw [← he]
  exact (hf.2.2.2 p hp _ htop.1).mp (htop.2 p hp)

end ZFVP
