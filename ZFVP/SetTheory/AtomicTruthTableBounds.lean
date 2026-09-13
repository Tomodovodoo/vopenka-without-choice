import ZFVP.SetTheory.BoundedAtomicTruth
import ZFVP.SetTheory.CnAbsoluteness

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem atomicTruthTable_exists_subset_support {U P : V} [hU : IsCodingSupport U]
    (hP : P ⊆ U) (R : V) : ∃ H : V, H ⊆ U ∧ IsAtomicTruthTable P R U H := by
  obtain ⟨H, hH⟩ := atomicTruthTable_exists P R U (transitive_subnameClosed hU.toIsTransitive)
  let K := H ∩ U
  have hentry {σ τ p : V} (hσ : σ ∈ U) (hτ : τ ∈ U) (hp : p ∈ P) :
      ⟨⟨σ, τ⟩ₖ, p⟩ₖ ∈ K ↔ ⟨⟨σ, τ⟩ₖ, p⟩ₖ ∈ H := by
    have ht := hU.kpair_closed _ (hU.kpair_closed σ hσ τ hτ) p (hP p hp)
    simp [K, ht]
  have hsets {σ τ : V} (hσ : σ ∈ U) (hτ : τ ∈ U) :
      atomicTruthSet P K σ τ = atomicTruthSet P H σ τ := by
    apply mem_ext
    intro p
    rw [mem_atomicTruthSet_iff, mem_atomicTruthSet_iff]
    exact and_congr_right fun hp ↦ hentry hσ hτ hp
  refine ⟨K, ?_, ?_⟩
  · intro z hz
    exact (mem_inter_iff.mp hz).2
  · intro σ hσ τ hτ p hp
    rw [hentry hσ hτ hp, hH σ hσ τ hτ p hp]
    apply atomicEqualityTest_congr
    intro υ s hs ν t ht
    exact (hsets (subname_pair_components_mem_transitive hσ hs).1
      (subname_pair_components_mem_transitive hτ ht).1).symm

theorem Cn.exists_atomicTruthTable_mem_successor {δ P : V} (hδ : Cn 1 δ)
    (hP : P ∈ hierarchy δ) (R : V) :
    ∃ H ∈ hierarchy (succ δ), IsAtomicTruthTable P R (hierarchy δ) H := by
  let := hδ.ordinal
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff 0 δ).mp hδ).2.support
  obtain ⟨H, hsub, hH⟩ := atomicTruthTable_exists_subset_support ((hierarchy_transitive δ).transitive P hP) R
  exact ⟨H, by simpa only [hierarchy_succ, mem_power_iff] using hsub, hH⟩

end ZFVP
