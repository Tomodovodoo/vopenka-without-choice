import ZFVP.SetTheory.SparseAppend
import ZFVP.SetTheory.ForcingPullbackOrder
import ZFVP.ModelTheory.ForcingIsomorphismComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def sparsePairCarrier (a P W : V) : V :=
  {q ∈ ℘ ((⋃ˢ P) ∪ ({a} ×ˢ W)); IsSparseFunctionOn (succ a) q ∧ q ↾ a ∈ P ∧ q ‘ a ∈ W}

instance sparsePairCarrier_definable : ℒₛₑₜ-function₃[V] sparsePairCarrier := by
  have h : ℒₛₑₜ-relation₄[V] (fun C a P W ↦ ∀ q, q ∈ C ↔
    q ⊆ ((⋃ˢ P) ∪ ({a} ×ˢ W)) ∧ IsSparseFunctionOn (succ a) q ∧ q ↾ a ∈ P ∧ q ‘ a ∈ W) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = sparsePairCarrier (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [sparsePairCarrier, mem_sep_iff, mem_power_iff]

theorem sparseAppend_subset_pairBound {a P W p τ : V} (hp : p ∈ P) (hτ : τ ∈ W) :
    sparseAppend a p τ ⊆ (⋃ˢ P) ∪ ({a} ×ˢ W) := by
  classical
  have hOld : p ⊆ (⋃ˢ P) ∪ ({a} ×ˢ W) :=
    fun z hz ↦ mem_union_iff.mpr (Or.inl (mem_sUnion_iff.mpr ⟨p, hp, hz⟩))
  by_cases he : τ = ∅
  · rwa [he, sparseAppend_empty]
  · rw [sparseAppend_nonempty he]
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact mem_union_iff.mpr (Or.inr (kpair_mem_iff.mpr ⟨by simp, hτ⟩))
    · exact hOld z hz

theorem mem_sparsePairCarrier_iff {a P W q : V} :
    q ∈ sparsePairCarrier a P W ↔ IsSparseFunctionOn (succ a) q ∧ q ↾ a ∈ P ∧ q ‘ a ∈ W := by
  constructor
  · intro hq
    exact (mem_sep_iff.mp hq).2
  · rintro ⟨hq, hp, hτ⟩
    refine mem_sep_iff.mpr ⟨mem_power_iff.mpr ?_, hq, hp, hτ⟩
    rw [← sparseAppend_reconstruct hq]
    exact sparseAppend_subset_pairBound hp hτ

theorem sparseAppend_mem_pairCarrier {a P W p τ : V}
    (hP : ∀ p ∈ P, IsSparseFunctionOn a p) (hp : p ∈ P) (hτ : τ ∈ W) :
    sparseAppend a p τ ∈ sparsePairCarrier a P W := by
  have hsp := hP p hp
  let := hsp.1
  exact mem_sparsePairCarrier_iff.mpr ⟨hsp.sparseAppend,
    (sparseAppend_restrict hsp.2.1).symm ▸ hp, (sparseAppend_value_new hsp.2.1).symm ▸ hτ⟩

noncomputable def sparsePairDecodeValue (a q : V) : V := ⟨q ↾ a, q ‘ a⟩ₖ

instance sparsePairDecodeValue_definable : ℒₛₑₜ-function₂[V] sparsePairDecodeValue := by
  unfold sparsePairDecodeValue
  definability

noncomputable def sparsePairDecode (a P W : V) : V :=
  definableGraph (sparsePairCarrier a P W) (sparsePairDecodeValue a) (by definability)

instance sparsePairDecode_definable : ℒₛₑₜ-function₃[V] sparsePairDecode := by
  have h : ℒₛₑₜ-relation₄[V] (fun f a P W ↦ ∀ z, z ∈ f ↔
    ∃ q ∈ sparsePairCarrier a P W, z = ⟨q, sparsePairDecodeValue a q⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = sparsePairDecode (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [sparsePairDecode, mem_definableGraph_iff]

theorem sparsePairDecode_value {a P W q : V} (hq : q ∈ sparsePairCarrier a P W) :
    (sparsePairDecode a P W) ‘ q = ⟨q ↾ a, q ‘ a⟩ₖ := value_definableGraph _ _ _ hq

theorem sparsePairDecode_append {a P W p τ : V}
    (hP : ∀ p ∈ P, IsSparseFunctionOn a p) (hp : p ∈ P) (hτ : τ ∈ W) :
    (sparsePairDecode a P W) ‘ (sparseAppend a p τ) = ⟨p, τ⟩ₖ := by
  let := (hP p hp).1
  rw [sparsePairDecode_value (sparseAppend_mem_pairCarrier hP hp hτ),
    sparseAppend_restrict (hP p hp).2.1, sparseAppend_value_new (hP p hp).2.1]

theorem sparsePairDecode_isomorphism {a P W R : V}
    (hP : ∀ p ∈ P, IsSparseFunctionOn a p) :
    IsForcingIsomorphism (sparsePairCarrier a P W)
      (forcingPullbackOrder (sparsePairCarrier a P W) R (sparsePairDecode a P W))
      (P ×ˢ W) R (sparsePairDecode a P W) := by
  have hfun : sparsePairDecode a P W ∈ (P ×ˢ W) ^ sparsePairCarrier a P W := by
    apply definableGraph_mem_function_of_mapsTo
    intro q hq
    have hh := mem_sparsePairCarrier_iff.mp hq
    exact kpair_mem_iff.mpr hh.2
  refine ⟨hfun, ?_, ?_, ?_⟩
  · intro q r z hqz hrz
    obtain ⟨hq, hzq⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hqz
    obtain ⟨hr, hzr⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hrz
    have he := congrArg (fun z : V ↦ sparseAppend a (kpair.π₁ z) (kpair.π₂ z)) (hzq.symm.trans hzr)
    simpa only [sparsePairDecodeValue, kpair.π₁_kpair, kpair.π₂_kpair,
      sparseAppend_reconstruct (mem_sparsePairCarrier_iff.mp hq).1,
      sparseAppend_reconstruct (mem_sparsePairCarrier_iff.mp hr).1] using he
  · apply SetTheory.subset_antisymm (range_subset_of_mem_function hfun)
    intro z hz
    obtain ⟨p, hp, τ, hτ, rfl⟩ := mem_prod_iff.mp hz
    have hq := sparseAppend_mem_pairCarrier hP hp hτ
    have he := sparsePairDecode_append hP hp hτ
    exact he ▸ value_mem_range hfun hq
  · intro q hq r hr
    simp only [mem_forcingPullbackOrder_iff, hq, hr, true_and]

noncomputable def sparsePairEncode (a P W : V) : V := converseGraph (sparsePairDecode a P W)

instance sparsePairEncode_definable : ℒₛₑₜ-function₃[V] sparsePairEncode := by
  unfold sparsePairEncode
  definability

theorem sparsePairEncode_isomorphism {a P W R : V}
    (hP : ∀ p ∈ P, IsSparseFunctionOn a p) :
    IsForcingIsomorphism (P ×ˢ W) R (sparsePairCarrier a P W)
      (forcingPullbackOrder (sparsePairCarrier a P W) R (sparsePairDecode a P W))
      (sparsePairEncode a P W) := (sparsePairDecode_isomorphism hP).inverse

theorem sparsePairEncode_value {a P W p τ : V}
    (hP : ∀ p ∈ P, IsSparseFunctionOn a p) (hp : p ∈ P) (hτ : τ ∈ W) :
    (sparsePairEncode a P W) ‘ ⟨p, τ⟩ₖ = sparseAppend a p τ := by
  have he := (sparsePairDecode_isomorphism (R := ∅) hP).inverse_value (sparseAppend_mem_pairCarrier hP hp hτ)
  rwa [sparsePairDecode_append hP hp hτ] at he

theorem sparsePairEncode_value_of_mem {a P W z : V}
    (hP : ∀ p ∈ P, IsSparseFunctionOn a p) (hz : z ∈ P ×ˢ W) :
    (sparsePairEncode a P W) ‘ z = sparseAppend a (kpair.π₁ z) (kpair.π₂ z) := by
  obtain ⟨p, hp, τ, hτ, rfl⟩ := mem_prod_iff.mp hz
  simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using sparsePairEncode_value hP hp hτ

theorem sparsePairCarrier_subset_hierarchy {a P W κ : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (ha : a ∈ hierarchy κ)
    (hP : P ⊆ hierarchy κ) (hW : W ⊆ hierarchy κ) : sparsePairCarrier a P W ⊆ hierarchy κ := by
  intro q hq
  obtain ⟨hs, hp, hτ⟩ := mem_sparsePairCarrier_iff.mp hq
  rw [← sparseAppend_reconstruct hs]
  exact sparseAppend_mem_hierarchy_limit hκ ha (hP _ hp) (hW _ hτ)

theorem sparsePairCarrier_mem_hierarchy {a P W κ : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (ha : a ∈ hierarchy κ)
    (hP : P ∈ hierarchy κ) (hW : W ∈ hierarchy κ) : sparsePairCarrier a P W ∈ hierarchy κ := by
  have hsing : ({a} : V) ∈ hierarchy κ := by simpa using pair_mem_hierarchy_limit hκ ha ha
  have hprod := prod_mem_hierarchy_limit hκ hsing hW
  have hbound := sUnion_mem_hierarchy_limit hκ
    (pair_mem_hierarchy_limit hκ (sUnion_mem_hierarchy_limit hκ hP) hprod)
  rw [pair_eq_doubleton] at hbound
  exact subset_mem_hierarchy_limit hκ (power_mem_hierarchy_limit hκ hbound) sep_subset

end ZFVP
