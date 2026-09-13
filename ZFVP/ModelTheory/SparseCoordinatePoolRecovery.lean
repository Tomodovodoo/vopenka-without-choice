import ZFVP.ModelTheory.WoodinSparseBaseRecovery

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def sparseCoordinatePool (S a : V) : V :=
  repl (fun p ↦ p ‘ a) (by definability) S

theorem mem_sparseCoordinatePool_iff {S a τ : V} :
    τ ∈ sparseCoordinatePool S a ↔ ∃ p ∈ S, τ = p ‘ a :=
  repl_spec (by definability)

instance sparseCoordinatePool_definable : ℒₛₑₜ-function₂[V] sparseCoordinatePool := by
  have hd : ℒₛₑₜ-relation₃[V] (fun W S a ↦ ∀ τ, τ ∈ W ↔ ∃ p ∈ S, τ = p ‘ a) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = sparseCoordinatePool (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_sparseCoordinatePool_iff]

theorem sparsePairCarrier_pool_recovery {a P W : V}
    (hsp : ∀ p ∈ P, IsSparseFunctionOn a p) (hP : IsNonempty P) :
    sparseCoordinatePool (sparsePairCarrier a P W) a = W := by
  apply mem_ext
  intro τ
  rw [mem_sparseCoordinatePool_iff]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (mem_sparsePairCarrier_iff.mp hp).2.2
  · intro hτ
    obtain ⟨p, hp⟩ := hP
    have hs := hsp p hp
    let := hs.1
    exact ⟨sparseAppend a p τ, sparseAppend_mem_pairCarrier hsp hp hτ,
      (sparseAppend_value_new hs.2.1).symm⟩

theorem sparseCoordinatePool_mono {S T a : V} (hST : S ⊆ T) :
    sparseCoordinatePool S a ⊆ sparseCoordinatePool T a := by
  intro τ hτ
  obtain ⟨p, hp, he⟩ := mem_sparseCoordinatePool_iff.mp hτ
  exact mem_sparseCoordinatePool_iff.mpr ⟨p, hST p hp, he⟩

theorem function_restrict_value_at {p a b : V} [IsFunction p] (ha : a ∈ b) :
    (p ↾ b) ‘ a = p ‘ a := by
  classical
  by_cases hd : a ∈ domain p
  · exact value_restrict hd ha
  · rw [value_eq_empty_of_not_mem_domain hd]
    apply value_eq_empty_of_not_mem_domain
    intro h
    obtain ⟨y, hy⟩ := mem_domain_iff.mp h
    exact hd (mem_domain_of_kpair_mem (kpair_mem_restrict_iff.mp hy).1)

theorem sparseCoordinatePool_restriction {S T a b : V}
    (hST : S ⊆ T) (hT : ∀ p ∈ T, IsFunction p)
    (hres : ∀ p ∈ T, p ↾ b ∈ S) (ha : a ∈ b) :
    sparseCoordinatePool S a = sparseCoordinatePool T a := by
  apply SetTheory.subset_antisymm (sparseCoordinatePool_mono hST)
  intro τ hτ
  obtain ⟨p, hp, rfl⟩ := mem_sparseCoordinatePool_iff.mp hτ
  let := hT p hp
  exact mem_sparseCoordinatePool_iff.mpr ⟨p ↾ b, hres p hp, (function_restrict_value_at ha).symm⟩

theorem sparseCoordinatePool_subset_hierarchy {S a δ : V} [IsOrdinal δ]
    (h0 : (∅ : V) ∈ hierarchy δ) (hS : S ⊆ hierarchy δ)
    (hf : ∀ p ∈ S, IsFunction p) :
    sparseCoordinatePool S a ⊆ hierarchy δ := by
  classical
  let := hierarchy_transitive δ
  intro τ hτ
  obtain ⟨p, hp, rfl⟩ := mem_sparseCoordinatePool_iff.mp hτ
  let := hf p hp
  by_cases ha : a ∈ domain p
  · exact (kpair_components_mem_transitive
      ((hierarchy_transitive δ).mem_trans (kpair_value_mem ha) (hS p hp))).2
  · rwa [value_eq_empty_of_not_mem_domain ha]

end ZFVP
