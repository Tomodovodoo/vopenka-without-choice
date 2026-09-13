import ZFVP.SetTheory.ForcingSequenceNames
import ZFVP.SetTheory.ForcingNameHierarchy
import ZFVP.SetTheory.DirectLimitClosure

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingName_sUnion {P B : V} (hB : ∀ τ ∈ B, IsForcingName P τ) :
    IsForcingName P (⋃ˢ B) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨τ, hτ, hzτ⟩ := mem_sUnion_iff.mp hz
  exact (forcingName_iff _ _).mp (hB τ hτ) z hzτ

theorem IsNameSequence.union_isName {P s : V} [IsFunction s] (hs : IsNameSequence P s) :
    IsForcingName P (⋃ˢ range s) := by
  apply forcingName_sUnion
  intro τ hτ
  obtain ⟨i, hiτ⟩ := mem_range_iff.mp hτ
  rw [← value_eq_of_kpair_mem hiτ]
  exact hs i (mem_domain_of_kpair_mem hiτ)

theorem forcingNameHierarchy_sequence_union {P δ α s : V} [IsOrdinal δ]
    (hα : α ∈ internalCofinality δ) (hs : s ∈ (forcingNameHierarchy P δ) ^ α) :
    ⋃ˢ range s ∈ forcingNameHierarchy P δ := by
  let L : V → V := leastOrdinalOrZero (fun τ β ↦ τ ⊆ forcingNameHierarchy P β ×ˢ P) (by definability)
  have hL (i : V) (hi : i ∈ α) : L (s ‘ i) ∈ δ ∧ s ‘ i ⊆ forcingNameHierarchy P (L (s ‘ i)) ×ˢ P := by
    obtain ⟨β, hβ, hsub⟩ := (mem_forcingNameHierarchy P δ _).mp (function_value_mem hs hi)
    let := IsOrdinal.of_mem hβ
    have hleast := leastOrdinalOrZero_spec (fun τ γ ↦ τ ⊆ forcingNameHierarchy P γ ×ˢ P)
      (by definability) (s ‘ i) ⟨β, inferInstance, hsub⟩
    exact ⟨ordinal_mem_of_subset_mem (hleast.2.2 β inferInstance hsub) hβ, hleast.2.1⟩
  let b := definableGraph α (fun i ↦ L (s ‘ i)) (by definability)
  have hb : b ∈ δ ^ α := definableGraph_mem_function_of_mapsTo _ _ _ _ (fun i hi ↦ (hL i hi).1)
  obtain ⟨k, hk, hbound⟩ := function_bounded_below_cofinality hα hb
  let := IsOrdinal.of_mem hk
  let := IsFunction.of_mem hs
  apply (mem_forcingNameHierarchy P δ _).mpr
  refine ⟨k, hk, ?_⟩
  intro z hz
  obtain ⟨τ, hτ, hzτ⟩ := mem_sUnion_iff.mp hz
  obtain ⟨i, hiτ⟩ := mem_range_iff.mp hτ
  have hi : i ∈ α := domain_eq_of_mem_function hs ▸ mem_domain_of_kpair_mem hiτ
  have hτi := value_eq_of_kpair_mem hiτ
  have hLi : L (s ‘ i) ∈ k := by simpa only [b, value_definableGraph _ _ _ hi] using hbound i hi
  have := IsOrdinal.of_mem hLi
  obtain ⟨ν, hν, p, hp, rfl⟩ := mem_prod_iff.mp ((hL i hi).2 z (hτi.symm ▸ hzτ))
  exact kpair_mem_iff.mpr ⟨forcingNameHierarchy_mono P (IsOrdinal.toIsTransitive.transitive _ hLi) ν hν, hp⟩

end ZFVP
