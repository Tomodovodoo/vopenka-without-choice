import ZFVP.ModelTheory.WoodinSparseDirectTransport
import ZFVP.ModelTheory.WoodinSparseInverseTop
import ZFVP.ModelTheory.WoodinSparseRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {θ c ξ : V} [IsOrdinal θ]

theorem woodinSparseDirectBase_subset_hierarchy
    (hc : IsForcingIterationCode θ c)
    (hP : ∀ i ∈ θ, (forcingCodeP c) ‘ i ⊆ hierarchy ξ) :
    woodinSparseDirectBase θ c ⊆ hierarchy ξ := by
  intro q hq
  obtain ⟨hq, i, hi, hdom⟩ := mem_woodinSparseDirectBase_iff.mp hq
  have hh := (mem_woodinSparseInverseBase_iff hc).mp hq
  let := hh.1.1
  have he : q ↾ (succ (woodinSourceIndex i)) = q := IsFunction.restrict_eq_self _ _ hdom
  exact hP i hi q (he ▸ hh.2 i hi)

theorem woodinSparseDirectBase_subset_hierarchy_of_rows [IsOrdinal ξ]
    (hc : IsForcingIterationCode θ c)
    (hP : ∀ i ∈ θ, (forcingCodeP c) ‘ i ∈ hierarchy ξ) :
    woodinSparseDirectBase θ c ⊆ hierarchy ξ :=
  woodinSparseDirectBase_subset_hierarchy hc
    (fun i hi _ hq ↦ (hierarchy_transitive ξ).mem_trans hq (hP i hi))

theorem woodinSparseDirectBase_mem_larger_hierarchy {δ : V} [IsOrdinal δ] [IsOrdinal ξ]
    (hc : IsForcingIterationCode θ c) (hξ : ∀ β ∈ ξ, succ β ∈ ξ)
    (hδξ : δ ∈ ξ) (hP : ∀ i ∈ θ, (forcingCodeP c) ‘ i ⊆ hierarchy δ) :
    woodinSparseDirectBase θ c ∈ hierarchy ξ := by
  apply subset_mem_hierarchy_limit hξ ?_ (woodinSparseDirectBase_subset_hierarchy hc hP)
  rw [mem_hierarchy_iff_rank_mem, rank_hierarchy]
  exact hδξ

variable (hc : IsForcingIterationCode θ c) (h0 : ∅ ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ)
variable (hsp : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p)
variable (hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
  ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)))
variable (hE : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ (forcingCodeP c) ‘ i,
  ((forcingCodeE c) ‘ ⟨i, j⟩ₖ) ‘ p = p)

private theorem sparseThreadOrder_subset' (θ b R C : V) : sparseThreadOrder θ b R C ⊆ C ×ˢ C := sep_subset

include hc h0 hlim hsp hπ hE in
theorem woodinSparseDirect_preorder :
    IsForcingPreorder (woodinSparseDirectBase θ c) (woodinSparseDirectOrder θ c) :=
  (woodinSparseDirectFlatten_isomorphism hc h0 hlim hsp hπ hE).target_preorder
    (hc.system.directColumn h0 hc.subset_universe).order.preorder (sparseThreadOrder_subset' _ _ _ _)

include hc h0 hsp hπ in
theorem woodinSparseDirectFlatten_top (ht : ∀ i ∈ θ, (forcingCodet c) ‘ i = ∅) :
    (woodinSparseDirectFlatten θ c) ‘ (forcingInverseCodeTop θ c) = ∅ := by
  have htop := (hc.system.directColumn h0 hc.subset_universe).tops.top.1
  have htop' : forcingInverseCodeTop θ c ∈ forcingDirectLimit θ (forcingCodeP c) (forcingCodeπ c) (forcingCodeE c) (forcingCodeUniverse c) := htop
  rw [woodinSparseDirectFlatten_value htop']
  have he := woodinSparseInverseFlatten_top hc h0 hsp hπ ht
  rwa [woodinSparseInverseFlatten_value hsp hπ (forcingDirectLimit_subset _ _ _ _ _ _ htop')] at he

include hc h0 hlim hsp hπ hE in
theorem woodinSparseDirect_empty_top (ht : ∀ i ∈ θ, (forcingCodet c) ‘ i = ∅) :
    IsForcingTop (woodinSparseDirectBase θ c) (woodinSparseDirectOrder θ c) ∅ := by
  have hf := woodinSparseDirectFlatten_isomorphism hc h0 hlim hsp hπ hE
  have htop := (hc.system.directColumn h0 hc.subset_universe).tops.top
  have he := woodinSparseDirectFlatten_top hc h0 hsp hπ ht
  refine ⟨he ▸ function_value_mem hf.1 htop.1, ?_⟩
  intro q hq
  obtain ⟨p, hp, rfl⟩ := hf.surjective q hq
  rw [← he]
  exact (hf.2.2.2 p hp _ htop.1).mp (htop.2 p hp)

theorem woodinSparseDirectBase_at_cutoff {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hc : IsForcingIterationCode θ c) (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hP : ∀ i ∈ θ, ∀ δ : V, IsChoicelessInaccessible δ →
      (woodinIterationCardinalPrefix θ) ‘ i ∈ δ → (forcingCodeP c) ‘ i ∈ hierarchy δ) :
    IsChoicelessInaccessible θ ∧ woodinSparseDirectBase θ c ⊆ hierarchy θ := by
  have hs := woodinIterationPrefix_of_stages
    (fun i hi ↦ ((woodinIterationExit hΩ hAC).2.1 i (hθ i hi)).1)
  have he := hs.index_eq_regular_limit hlim hinac.regular
  have ht : IsChoicelessInaccessible θ := he.symm ▸ hinac
  refine ⟨ht, woodinSparseDirectBase_subset_hierarchy_of_rows hc ?_⟩
  intro i hi
  apply hP i hi θ ht
  exact (congrArg (fun z ↦ (woodinIterationCardinalPrefix θ) ‘ i ∈ z) he).mpr
    (hs.cardinal_mem_limit hlim hi)
end ZFVP





