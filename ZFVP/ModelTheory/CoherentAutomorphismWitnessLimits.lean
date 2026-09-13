import ZFVP.ModelTheory.CoherentAutomorphismWitnessRecursion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {θ c a b δ H W : V} [IsOrdinal θ]

theorem IsCoherentAutomorphismWitnessHistory.bounds_inverse
    (h : IsCoherentAutomorphismWitnessHistory θ c a b δ H W)
    (hc : IsForcingIterationCode θ c) : W ∈ forcingInverseCodePoset θ c := by
  apply (mem_forcingInverseLimit_iff _ _ _ _ _).mpr
  refine ⟨h.boundsTable.mem_function (fun i hi ↦ hc.subset_universe i hi _ (h.mem i hi)), h.mem, ?_⟩
  intro j hj i hij hi
  let := IsOrdinal.of_mem hj
  exact h.proj i hi j hj (IsOrdinal.toIsTransitive.transitive _ hij)

theorem IsCoherentAutomorphismWitnessHistory.bounds_common
    (h : IsCoherentAutomorphismWitnessHistory θ c a b δ H W)
    (hc : IsForcingIterationCode θ c)
    (ha : a ∈ forcingInverseCodePoset θ c) (hb : b ∈ forcingInverseCodePoset θ c) :
    ⟨W, forcingThreadAction θ H a⟩ₖ ∈ forcingInverseCodeOrder θ c ∧
      ⟨W, b⟩ₖ ∈ forcingInverseCodeOrder θ c := by
  constructor
  · apply (mem_forcingThreadOrder_iff _ _ _ _ _).mpr
    refine ⟨h.bounds_inverse hc, h.automorphism.maps_inverse hc ha, ?_⟩
    intro i hi
    rw [forcingThreadAction_value hi]
    exact h.left i hi
  · exact (mem_forcingThreadOrder_iff _ _ _ _ _).mpr ⟨h.bounds_inverse hc, hb, h.right⟩

omit [IsOrdinal θ] in
theorem IsCoherentAutomorphismWitnessHistory.union_support
    (h : IsCoherentAutomorphismWitnessHistory θ c a b δ H W)
    {A : V} (hA : ∀ i ∈ θ, domain (a ‘ i) ∪ domain (b ‘ i) ⊆ A) :
    domain (⋃ˢ range W) ⊆ A := by
  let := h.boundsTable.function
  intro x hx
  obtain ⟨w, hw, hx⟩ := (mem_domain_sUnion_iff (range W) x).mp hx
  obtain ⟨i, hiw⟩ := mem_range_iff.mp hw
  have hi : i ∈ θ := h.boundsTable.domain_eq ▸ mem_domain_of_kpair_mem hiw
  rw [← value_eq_of_kpair_mem hiw] at hx
  exact hA i hi x (h.support i hi x hx)

variable (hc : IsForcingIterationCode θ c) (h0 : ∅ ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ)
variable (hsp : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p)
variable (hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
  ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)))

include hc h0 hlim hsp hπ in
theorem IsCoherentAutomorphismWitnessHistory.union_mem
    (h : IsCoherentAutomorphismWitnessHistory θ c a b δ H W) :
    ⋃ˢ range W ∈ woodinSparseInverseBase θ c := by
  rw [← woodinSparseInverseFlatten_value hsp hπ (h.bounds_inverse hc)]
  exact function_value_mem (woodinSparseInverseFlatten_isomorphism hc h0 hlim hsp hπ).1
    (h.bounds_inverse hc)

include hc hsp hπ in
theorem IsCoherentAutomorphismWitnessHistory.union_restrict
    (h : IsCoherentAutomorphismWitnessHistory θ c a b δ H W) {i : V} (hi : i ∈ θ) :
    (⋃ˢ range W) ↾ (succ (woodinSourceIndex i)) = W ‘ i := by
  rw [← woodinSparseInverseFlatten_value hsp hπ (h.bounds_inverse hc)]
  exact woodinSparseInverseFlatten_restrict hsp hπ (h.bounds_inverse hc) hi

include hc h0 hlim hsp hπ in
theorem IsCoherentAutomorphismWitnessHistory.union_common
    (h : IsCoherentAutomorphismWitnessHistory θ c a b δ H W)
    (ha : a ∈ forcingInverseCodePoset θ c) (hb : b ∈ forcingInverseCodePoset θ c) :
    ⟨⋃ˢ range W, (woodinSparseInverseAutomorphism θ c H) ‘ ((woodinSparseInverseFlatten θ c) ‘ a)⟩ₖ
        ∈ woodinSparseInverseOrder θ c ∧
      ⟨⋃ˢ range W, (woodinSparseInverseFlatten θ c) ‘ b⟩ₖ ∈ woodinSparseInverseOrder θ c := by
  have hf := woodinSparseInverseFlatten_isomorphism hc h0 hlim hsp hπ
  have hw := h.bounds_inverse hc
  have hh := h.bounds_common hc ha hb
  rw [← woodinSparseInverseFlatten_value hsp hπ hw,
    woodinSparseInverseAutomorphism_flatten hc h.automorphism h0 hlim hsp hπ ha]
  exact ⟨(hf.2.2.2 _ hw _ (h.automorphism.maps_inverse hc ha)).mp hh.1,
    (hf.2.2.2 _ hw _ hb).mp hh.2⟩

include hc h0 hlim hsp hπ in
theorem IsCoherentAutomorphismWitnessHistory.union_mem_direct
    (h : IsCoherentAutomorphismWitnessHistory θ c a b δ H W)
    {k : V} (hk : k ∈ θ)
    (hA : ∀ i ∈ θ, domain (a ‘ i) ∪ domain (b ‘ i) ⊆ succ (woodinSourceIndex k)) :
    ⋃ˢ range W ∈ woodinSparseDirectBase θ c :=
  mem_woodinSparseDirectBase_iff.mpr ⟨h.union_mem hc h0 hlim hsp hπ, k, hk, h.union_support hA⟩

variable (hE : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ (forcingCodeP c) ‘ i,
  ((forcingCodeE c) ‘ ⟨i, j⟩ₖ) ‘ p = p)

include hc h0 hlim hsp hπ hE in
theorem IsCoherentAutomorphismWitnessHistory.bounds_direct
    (h : IsCoherentAutomorphismWitnessHistory θ c a b δ H W)
    {k : V} (hk : k ∈ θ)
    (hA : ∀ i ∈ θ, domain (a ‘ i) ∪ domain (b ‘ i) ⊆ succ (woodinSourceIndex k)) :
    W ∈ forcingDirectLimit θ (forcingCodeP c) (forcingCodeπ c) (forcingCodeE c) (forcingCodeUniverse c) := by
  have hw : W ∈ sparseRestrictionThreads θ (woodinSparseBounds θ) (forcingCodeP c) (forcingCodeUniverse c) := by
    rw [← woodinSparseInverse_threads hsp hπ]
    exact h.bounds_inverse hc
  have hh := woodinSparseDirectDecodeValue_mem hc hsp hπ hE
    (h.union_mem_direct hc h0 hlim hsp hπ hk hA)
  simpa only [sparseThreadDecodeValue_union hw] using hh

include hc h0 hlim hsp hπ hE in
theorem IsCoherentAutomorphismWitnessHistory.union_common_direct
    (h : IsCoherentAutomorphismWitnessHistory θ c a b δ H W)
    (ha : a ∈ forcingDirectLimit θ (forcingCodeP c) (forcingCodeπ c) (forcingCodeE c) (forcingCodeUniverse c))
    (hb : b ∈ forcingDirectLimit θ (forcingCodeP c) (forcingCodeπ c) (forcingCodeE c) (forcingCodeUniverse c))
    {k : V} (hk : k ∈ θ)
    (hA : ∀ i ∈ θ, domain (a ‘ i) ∪ domain (b ‘ i) ⊆ succ (woodinSourceIndex k)) :
    ⟨⋃ˢ range W, (woodinSparseDirectAutomorphism θ c H) ‘ ((woodinSparseDirectFlatten θ c) ‘ a)⟩ₖ
        ∈ woodinSparseDirectOrder θ c ∧
      ⟨⋃ˢ range W, (woodinSparseDirectFlatten θ c) ‘ b⟩ₖ ∈ woodinSparseDirectOrder θ c := by
  have hf := woodinSparseDirectFlatten_isomorphism hc h0 hlim hsp hπ hE
  have hw := h.bounds_direct hc h0 hlim hsp hπ hE hk hA
  have hma := h.automorphism.maps_direct hc ha
  rw [← woodinSparseDirectFlatten_value hw,
    woodinSparseDirectAutomorphism_flatten hc h.automorphism h0 hlim hsp hπ hE ha]
  constructor
  · apply (hf.2.2.2 _ hw _ hma).mp
    apply (mem_forcingThreadOrder_iff _ _ _ _ _).mpr
    refine ⟨hw, hma, ?_⟩
    intro i hi
    rw [forcingThreadAction_value hi]
    exact h.left i hi
  · exact (hf.2.2.2 _ hw _ hb).mp ((mem_forcingThreadOrder_iff _ _ _ _ _).mpr ⟨hw, hb, h.right⟩)

end ZFVP
