import ZFVP.ModelTheory.WoodinSparseInverseBase

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSparseDirectBase (θ c : V) : V :=
  {q ∈ woodinSparseInverseBase θ c; ∃ i ∈ θ, domain q ⊆ succ (woodinSourceIndex i)}

noncomputable def woodinSparseDirectOrder (θ c : V) : V :=
  sparseThreadOrder θ (woodinSparseBounds θ) (forcingCodeR c) (woodinSparseDirectBase θ c)

noncomputable def woodinSparseDirectFlatten (θ c : V) : V :=
  definableGraph (forcingDirectLimit θ (forcingCodeP c) (forcingCodeπ c) (forcingCodeE c) (forcingCodeUniverse c))
    (fun t ↦ ⋃ˢ range t) (by definability)

noncomputable def woodinSparseDirectDecode (θ c : V) : V :=
  definableGraph (woodinSparseDirectBase θ c) (sparseThreadDecodeValue θ (woodinSparseBounds θ)) (by definability)

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

instance woodinSparseDirectBase_definable : ℒₛₑₜ-function₂[V] woodinSparseDirectBase := by
  have h : ℒₛₑₜ-relation₃[V] (fun C θ c ↦ ∀ q, q ∈ C ↔
      q ∈ woodinSparseInverseBase θ c ∧ ∃ i ∈ θ, domain q ⊆ succ (woodinSourceIndex i)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = woodinSparseDirectBase (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [woodinSparseDirectBase, mem_sep_iff]

instance woodinSparseDirectOrder_definable : ℒₛₑₜ-function₂[V] woodinSparseDirectOrder := by
  unfold woodinSparseDirectOrder
  definability

instance woodinSparseDirectFlatten_definable : ℒₛₑₜ-function₂[V] woodinSparseDirectFlatten := by
  have h : ℒₛₑₜ-relation₃[V] (fun f θ c ↦ ∀ z, z ∈ f ↔
      ∃ t ∈ forcingDirectLimit θ (forcingCodeP c) (forcingCodeπ c) (forcingCodeE c) (forcingCodeUniverse c),
        z = ⟨t, ⋃ˢ range t⟩ₖ) := by
    simp only [forcingDirectLimit, mem_sep_iff]
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = woodinSparseDirectFlatten (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [woodinSparseDirectFlatten, mem_definableGraph_iff]

instance woodinSparseDirectDecode_definable : ℒₛₑₜ-function₂[V] woodinSparseDirectDecode := by
  have h : ℒₛₑₜ-relation₃[V] (fun f θ c ↦ ∀ z, z ∈ f ↔
      ∃ q ∈ woodinSparseDirectBase θ c, z = ⟨q, sparseThreadDecodeValue θ (woodinSparseBounds θ) q⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = woodinSparseDirectDecode (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [woodinSparseDirectDecode, mem_definableGraph_iff]

theorem mem_woodinSparseDirectBase_iff {θ c q : V} :
    q ∈ woodinSparseDirectBase θ c ↔ q ∈ woodinSparseInverseBase θ c ∧
      ∃ i ∈ θ, domain q ⊆ succ (woodinSourceIndex i) := mem_sep_iff

variable {θ c : V} [IsOrdinal θ]
local notation "D" => forcingDirectLimit θ (forcingCodeP c) (forcingCodeπ c) (forcingCodeE c) (forcingCodeUniverse c)

theorem woodinSparseDirect_union_of_support {t k : V}
    (hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
      ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)))
    (hE : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ (forcingCodeP c) ‘ i,
      ((forcingCodeE c) ‘ ⟨i, j⟩ₖ) ‘ p = p)
    (ht : t ∈ forcingInverseCodePoset θ c) (hk : IsThreadSupport θ (forcingCodeE c) t k) :
    ⋃ˢ range t = t ‘ k := by
  have hh := (mem_forcingInverseLimit_iff _ _ _ _ _).mp ht
  let := IsFunction.of_mem hh.1
  let := IsOrdinal.of_mem hk.1
  apply SetTheory.subset_antisymm
  · intro z hz
    obtain ⟨p, hp, hz⟩ := mem_sUnion_iff.mp hz
    obtain ⟨j, hjp⟩ := mem_range_iff.mp hp
    have hj : j ∈ θ := domain_eq_of_mem_function hh.1 ▸ mem_domain_of_kpair_mem hjp
    rw [← value_eq_of_kpair_mem hjp] at hz
    let := IsOrdinal.of_mem hj
    rcases IsOrdinal.mem_trichotomy j k with hjk | rfl | hkj
    · rw [← hh.2.2 k hk.1 j hjk hj, hπ j hj k hk.1 hjk _ (hh.2.1 k hk.1)] at hz
      exact restrict_subset _ _ _ hz
    · exact hz
    · have hkj' := IsOrdinal.toIsTransitive.transitive _ hkj
      rwa [hk.2 j hj hkj', hE k hk.1 j hj hkj' _ (hh.2.1 k hk.1)] at hz
  · intro z hz
    exact mem_sUnion_iff.mpr ⟨t ‘ k, value_mem_range hh.1 hk.1, hz⟩

private theorem sparse_bound_mono {i j : V} (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j) :
    succ (woodinSourceIndex i) ⊆ succ (woodinSourceIndex j) := by
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  rcases IsOrdinal.subset_iff.mp hij with rfl | hij
  · exact subset_refl _
  · simpa only [woodinSparseBounds_value hi, woodinSparseBounds_value hj] using woodinSparseBounds_mono hij hj

theorem woodinSparseDirectDecodeValue_supported {q k : V}
    (hc : IsForcingIterationCode θ c)
    (hE : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ (forcingCodeP c) ‘ i,
      ((forcingCodeE c) ‘ ⟨i, j⟩ₖ) ‘ p = p)
    (hq : q ∈ woodinSparseInverseBase θ c) (hk : k ∈ θ)
    (hdom : domain q ⊆ succ (woodinSourceIndex k)) :
    IsThreadSupport θ (forcingCodeE c) (sparseThreadDecodeValue θ (woodinSparseBounds θ) q) k := by
  have hh := (mem_woodinSparseInverseBase_iff hc).mp hq
  let := hh.1.1
  have he : q ↾ (succ (woodinSourceIndex k)) = q := IsFunction.restrict_eq_self _ _ hdom
  have hqk : q ∈ (forcingCodeP c) ‘ k := he ▸ hh.2 k hk
  refine ⟨hk, ?_⟩
  intro j hj hkj
  rw [sparseThreadDecodeValue_apply hj, sparseThreadDecodeValue_apply hk,
    woodinSparseBounds_value hj, woodinSparseBounds_value hk, he, hE k hk j hj hkj q hqk]
  exact IsFunction.restrict_eq_self _ _ (subset_trans hdom (sparse_bound_mono hk hj hkj))

theorem woodinSparseDirectDecodeValue_mem {q : V}
    (hc : IsForcingIterationCode θ c)
    (hsp : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p)
    (hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
      ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)))
    (hE : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ (forcingCodeP c) ‘ i,
      ((forcingCodeE c) ‘ ⟨i, j⟩ₖ) ‘ p = p)
    (hq : q ∈ woodinSparseDirectBase θ c) :
    sparseThreadDecodeValue θ (woodinSparseBounds θ) q ∈ D := by
  obtain ⟨hq, k, hk, hdom⟩ := mem_woodinSparseDirectBase_iff.mp hq
  have ht : sparseThreadDecodeValue θ (woodinSparseBounds θ) q ∈ forcingInverseCodePoset θ c := by
    rw [woodinSparseInverse_threads hsp hπ]
    exact sparseThreadDecodeValue_mem hq hc.subset_universe
  exact (mem_forcingDirectLimit_iff _ _ _ _ _ _).mpr
    ⟨ht, k, woodinSparseDirectDecodeValue_supported hc hE hq hk hdom⟩

theorem woodinSparseDirect_union_mem {t : V}
    (h0 : ∅ ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hsp : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p)
    (hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
      ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)))
    (hE : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ (forcingCodeP c) ‘ i,
      ((forcingCodeE c) ‘ ⟨i, j⟩ₖ) ‘ p = p)
    (ht : t ∈ D) : ⋃ˢ range t ∈ woodinSparseDirectBase θ c := by
  obtain ⟨ht, k, hk⟩ := (mem_forcingDirectLimit_iff _ _ _ _ _ _).mp ht
  have hthreads := ht
  rw [show forcingInverseLimit θ (forcingCodeP c) (forcingCodeπ c) (forcingCodeUniverse c) =
      forcingInverseCodePoset θ c from rfl, woodinSparseInverse_threads hsp hπ] at hthreads
  apply mem_woodinSparseDirectBase_iff.mpr
  refine ⟨sparseRestrictionThread_union_mem hthreads (fun i hi ↦ woodinSparseBounds_limit_subset h0 hlim hi),
    k, hk.1, ?_⟩
  rw [woodinSparseDirect_union_of_support hπ hE ht hk]
  exact (hsp k hk.1 _ (((mem_forcingInverseLimit_iff _ _ _ _ _).mp ht).2.1 k hk.1)).2.1

omit [IsOrdinal θ] in
theorem woodinSparseDirectFlatten_value {t : V} (ht : t ∈ D) :
    (woodinSparseDirectFlatten θ c) ‘ t = ⋃ˢ range t := value_definableGraph _ _ _ ht

omit [IsOrdinal θ] in
theorem woodinSparseDirectDecode_value {q : V} (hq : q ∈ woodinSparseDirectBase θ c) :
    (woodinSparseDirectDecode θ c) ‘ q = sparseThreadDecodeValue θ (woodinSparseBounds θ) q :=
  value_definableGraph _ _ _ hq

theorem woodinSparseDirectFlatten_decode {q : V}
    (hc : IsForcingIterationCode θ c)
    (hsp : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p)
    (hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
      ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)))
    (hE : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ (forcingCodeP c) ‘ i,
      ((forcingCodeE c) ‘ ⟨i, j⟩ₖ) ‘ p = p)
    (hq : q ∈ woodinSparseDirectBase θ c) :
    (woodinSparseDirectFlatten θ c) ‘ ((woodinSparseDirectDecode θ c) ‘ q) = q := by
  rw [woodinSparseDirectDecode_value hq,
    woodinSparseDirectFlatten_value (woodinSparseDirectDecodeValue_mem hc hsp hπ hE hq)]
  exact sparseThread_union_decodeValue
    ((mem_woodinSparseInverseBase_iff hc).mp (mem_woodinSparseDirectBase_iff.mp hq).1).1
    (fun _ hx ↦ woodinSparseBounds_cover hx)

theorem woodinSparseDirectDecode_flatten {t : V}
    (h0 : ∅ ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hsp : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p)
    (hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
      ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)))
    (hE : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ (forcingCodeP c) ‘ i,
      ((forcingCodeE c) ‘ ⟨i, j⟩ₖ) ‘ p = p)
    (ht : t ∈ D) : (woodinSparseDirectDecode θ c) ‘ ((woodinSparseDirectFlatten θ c) ‘ t) = t := by
  rw [woodinSparseDirectFlatten_value ht,
    woodinSparseDirectDecode_value (woodinSparseDirect_union_mem h0 hlim hsp hπ hE ht)]
  apply sparseThreadDecodeValue_union
  rw [← woodinSparseInverse_threads hsp hπ]
  exact forcingDirectLimit_subset _ _ _ _ _ _ ht

theorem woodinSparseDirectFlatten_isomorphism
    (hc : IsForcingIterationCode θ c) (h0 : ∅ ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hsp : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p)
    (hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
      ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)))
    (hE : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ (forcingCodeP c) ‘ i,
      ((forcingCodeE c) ‘ ⟨i, j⟩ₖ) ‘ p = p) :
    IsForcingIsomorphism D (forcingThreadOrder θ (forcingCodeR c) D)
      (woodinSparseDirectBase θ c) (woodinSparseDirectOrder θ c) (woodinSparseDirectFlatten θ c) := by
  have hf : woodinSparseDirectFlatten θ c ∈ (woodinSparseDirectBase θ c) ^ D :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun t ht ↦ woodinSparseDirect_union_mem h0 hlim hsp hπ hE ht)
  have hthreads {t : V} (ht : t ∈ D) : t ∈ sparseRestrictionThreads θ (woodinSparseBounds θ)
      (forcingCodeP c) (forcingCodeUniverse c) := by
    rw [← woodinSparseInverse_threads hsp hπ]
    exact forcingDirectLimit_subset _ _ _ _ _ _ ht
  refine ⟨hf, ?_, ?_, ?_⟩
  · intro t s z htz hsz
    obtain ⟨ht, hzt⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp htz
    obtain ⟨hs, hzs⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hsz
    have he := congrArg (sparseThreadDecodeValue θ (woodinSparseBounds θ)) (hzt.symm.trans hzs)
    simpa only [sparseThreadDecodeValue_union (hthreads ht), sparseThreadDecodeValue_union (hthreads hs)] using he
  · apply SetTheory.subset_antisymm (range_subset_of_mem_function hf)
    intro q hq
    have ht := woodinSparseDirectDecodeValue_mem hc hsp hπ hE hq
    have he : (woodinSparseDirectFlatten θ c) ‘ (sparseThreadDecodeValue θ (woodinSparseBounds θ) q) = q := by
      rw [woodinSparseDirectFlatten_value ht]
      exact sparseThread_union_decodeValue
        ((mem_woodinSparseInverseBase_iff hc).mp (mem_woodinSparseDirectBase_iff.mp hq).1).1
        (fun _ hx ↦ woodinSparseBounds_cover hx)
    exact he ▸ value_mem_range hf ht
  · intro t ht s hs
    rw [woodinSparseDirectFlatten_value ht, woodinSparseDirectFlatten_value hs]
    simp only [woodinSparseDirectOrder, mem_forcingThreadOrder_iff, mem_sparseThreadOrder_iff,
      ht, hs, woodinSparseDirect_union_mem h0 hlim hsp hπ hE ht,
      woodinSparseDirect_union_mem h0 hlim hsp hπ hE hs, true_and]
    constructor <;> intro h i hi <;>
      simpa only [sparseRestrictionThread_union_restrict (hthreads ht) hi,
        sparseRestrictionThread_union_restrict (hthreads hs) hi] using h i hi

end ZFVP
