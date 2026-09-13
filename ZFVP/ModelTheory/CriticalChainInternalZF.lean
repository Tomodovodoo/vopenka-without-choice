import ZFVP.ModelTheory.CriticalChainLimit
import ZFVP.ModelTheory.ElementaryCollection

/-! The union of the critical rank chain satisfies the full internal ZF schemas. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem function_mem_transitive_codomain {A B n b : V} [hA : IsTransitive A]
    (hb : b ∈ B ^ n) (hbA : b ∈ A) : b ∈ A ^ n := by
  let := IsFunction.of_mem hb
  have hbr : b ∈ range b ^ n := by
    rw [← domain_eq_of_mem_function hb]
    exact IsFunction.mem_function b
  apply mem_function_of_mem_function_of_subset hbr
  intro y hy
  obtain ⟨x, hxy⟩ := mem_range_iff.mp hy
  exact (kpair_components_mem_transitive (hA.mem_trans hxy hbA)).2

namespace CriticalSequence

variable {k : ℕ} {δ f κ : V} (hδ : Cn (k + 1) δ)
  (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
  (hκ : IsCriticalPoint (hierarchy δ) f κ)

include hδ h hκ

theorem omega_mem_limit : (ω : V) ∈ criticalLimit f κ := by
  let := limit_ordinal hδ h hκ
  have hκlim : κ ∈ criticalLimit f κ := by
    simpa using iterate_mem_limit hδ h hκ (by simp : (0 : V) ∈ ω)
  exact IsOrdinal.toIsTransitive.mem_trans
    (rankEmbedding_criticalPoint_rankCriterion hδ hδ h hκ).2.1 hκlim

theorem parameters_in_stage {n b a : V} (hn : n ∈ (ω : V))
    (hb : b ∈ hierarchy (criticalLimit f κ) ^ n) (ha : a ∈ hierarchy (criticalLimit f κ)) :
    ∃ i ∈ (ω : V), b ∈ hierarchy (criticalIterate f κ i) ^ n ∧
      a ∈ hierarchy (criticalIterate f κ i) := by
  let := limit_ordinal hδ h hκ
  have hs : ∀ β ∈ criticalLimit f κ, succ β ∈ criticalLimit f κ := fun _ ↦ limit_succ_closed hδ h hκ
  have hbmem := finiteSequence_mem_hierarchy_limit (omega_mem_limit hδ h hκ) hs
    ((mem_finiteSequences_iff _ _).mpr ⟨n, hn, hb⟩)
  have hp := kpair_mem_hierarchy_limit hs ha hbmem
  obtain ⟨i, hi, hpi⟩ := (rank_union_iff hδ h hκ _).mp hp
  let := (iterate_spec hδ h hκ hi).1
  let := hierarchy_transitive (criticalIterate f κ i)
  have hab := kpair_components_mem_transitive hpi
  exact ⟨i, hi, function_mem_transitive_codomain hb hab.2, hab.1⟩

theorem limit_internalCollection : InternalCollection (hierarchy (criticalLimit f κ)) := by
  intro n hn φ hφ b hb a ha htotal
  obtain ⟨i, hi, hbi, hai⟩ := parameters_in_stage hδ h hκ hn hb ha
  have hcrit := iterate_rankCriterion hδ h hκ hi
  let := hcrit.1
  let := hierarchy_transitive (criticalIterate f κ i)
  have hinc := limit_elementaryInclusion hδ h hκ hi
  obtain ⟨c, hc, hw⟩ := hinc.collection_instance
    (rank_internalCollection hcrit.2.2.1 hcrit.2.2.2) hn hφ hbi hai htotal
  exact ⟨c, hinc.subset _ hc, hw⟩

theorem limit_internalZFModel : IsInternalZFModel (hierarchy (criticalLimit f κ)) := by
  let := limit_ordinal hδ h hκ
  have hω := omega_mem_limit hδ h hκ
  have hs : ∀ β ∈ criticalLimit f κ, succ β ∈ criticalLimit f κ := fun _ ↦ limit_succ_closed hδ h hκ
  let := rankDomain_nonempty hω
  let := rankDomain_models_zermelo hω hs
  exact ⟨internalFixedZFAxioms_of_zermelo _, rank_internalSeparation hs,
    rank_internalReplacement_of_collection hs (limit_internalCollection hδ h hκ)⟩

end CriticalSequence

end ZFVP
