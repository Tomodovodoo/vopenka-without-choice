import ZFVP.SetTheory.WoodinSeedPrefix
import ZFVP.SetTheory.ForcingIterationInitial

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSourceIndex_cases {θ i : V} [IsOrdinal θ] (hi : i ∈ woodinSourceIndex θ) :
    i = ∅ ∨ ∃ α ∈ θ, i = woodinSourceIndex α := by
  by_cases hz : i = ∅
  · exact Or.inl hz
  · let := IsOrdinal.of_mem hi
    exact Or.inr ⟨woodinRecursiveIndex i, (woodinRecursiveIndex_mem_iff hz).mpr hi,
      (woodinSourceIndex_recursiveIndex i hz).symm⟩

theorem woodinSourceIndex_subset_nonzero {i j : V} [IsOrdinal i]
    (hij : woodinSourceIndex i ⊆ j) : j ≠ ∅ := by
  intro hz
  have hzero : (∅ : V) ∈ woodinSourceIndex i :=
    subset_ordinalAdd 1 i ∅ (by change (0 : V) ∈ succ 0; simp)
  have hh := hij ∅ hzero
  rw [hz] at hh
  exact not_mem_empty hh

theorem woodinSourceIndex_subset_recursive {i j : V} [IsOrdinal i] [IsOrdinal j]
    (hij : woodinSourceIndex i ⊆ j) : i ⊆ woodinRecursiveIndex j :=
  woodinSourceIndex_subset_iff.mp (by
    simpa only [woodinSourceIndex_recursiveIndex j (woodinSourceIndex_subset_nonzero hij)] using hij)

theorem woodinSeedProjections_zero_value {θ P π j p : V} [IsOrdinal θ]
    (hj : j ∈ woodinSourceIndex θ) (hp : p ∈ (woodinInsertSeed θ P {∅}) ‘ j) :
    ((woodinSeedProjections θ P π) ‘ ⟨∅, j⟩ₖ) ‘ p = ∅ := by
  rw [woodinSeedProjections, woodinSeedMatrix_zero hj, woodinSeedProjectionColumn_value hj hp]

theorem woodinSeedSections_zero_value {θ E t j : V} [IsOrdinal θ]
    (hj : j ∈ woodinSourceIndex θ) :
    ((woodinSeedSections θ E t) ‘ ⟨∅, j⟩ₖ) ‘ ∅ = (woodinInsertSeed θ t ∅) ‘ j := by
  rw [woodinSeedSections, woodinSeedMatrix_zero hj, woodinSeedSectionColumn_value hj]

theorem woodinSeed_top_mem {θ P t : V} [IsOrdinal θ]
    (ht : ∀ i ∈ θ, t ‘ i ∈ P ‘ i) :
    ∀ i ∈ woodinSourceIndex θ, (woodinInsertSeed θ t ∅) ‘ i ∈ (woodinInsertSeed θ P {∅}) ‘ i := by
  intro i hi
  rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
  · rw [woodinInsertSeed_zero, woodinInsertSeed_zero]
    simp
  · rw [woodinInsertSeed_at_sourceIndex ha, woodinInsertSeed_at_sourceIndex ha]
    exact ht a ha

theorem woodinSeed_projMaps {θ P π E : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) :
    ∀ i ∈ woodinSourceIndex θ, ∀ j ∈ woodinSourceIndex θ, i ⊆ j →
      ∀ p ∈ (woodinInsertSeed θ P {∅}) ‘ j,
      ((woodinSeedProjections θ P π) ‘ ⟨i, j⟩ₖ) ‘ p ∈ (woodinInsertSeed θ P {∅}) ‘ i := by
  intro i hi j hj hij p hp
  let := IsOrdinal.of_mem hj
  rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
  · rw [woodinSeedProjections_zero_value hj hp, woodinInsertSeed_zero]
    simp
  · let := IsOrdinal.of_mem ha
    have hjn := woodinSourceIndex_subset_nonzero hij
    have hrj := (woodinRecursiveIndex_mem_iff hjn).mpr hj
    rw [woodinInsertSeed_nonzero hj hjn] at hp
    rw [woodinSeedProjections, woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr ha) hj
      (woodinSourceIndex_nonzero a), woodinRecursiveIndex_sourceIndex, woodinInsertSeed_at_sourceIndex ha]
    exact h.projMaps a ha _ hrj (woodinSourceIndex_subset_recursive hij) p hp

theorem woodinSeed_secMaps {θ P π E t : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (ht : ∀ i ∈ θ, t ‘ i ∈ P ‘ i) :
    ∀ i ∈ woodinSourceIndex θ, ∀ j ∈ woodinSourceIndex θ, i ⊆ j →
      ∀ p ∈ (woodinInsertSeed θ P {∅}) ‘ i,
      ((woodinSeedSections θ E t) ‘ ⟨i, j⟩ₖ) ‘ p ∈ (woodinInsertSeed θ P {∅}) ‘ j := by
  intro i hi j hj hij p hp
  let := IsOrdinal.of_mem hj
  rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
  · rw [woodinInsertSeed_zero] at hp
    have he := mem_singleton_iff.mp hp
    subst p
    rw [woodinSeedSections_zero_value hj]
    exact woodinSeed_top_mem ht j hj
  · let := IsOrdinal.of_mem ha
    have hjn := woodinSourceIndex_subset_nonzero hij
    have hrj := (woodinRecursiveIndex_mem_iff hjn).mpr hj
    rw [woodinInsertSeed_at_sourceIndex ha] at hp
    rw [woodinSeedSections, woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr ha) hj
      (woodinSourceIndex_nonzero a), woodinRecursiveIndex_sourceIndex, woodinInsertSeed_nonzero hj hjn]
    exact h.secMaps a ha _ hrj (woodinSourceIndex_subset_recursive hij) p hp

theorem woodinSeed_tops {θ P R π E t : V} [IsOrdinal θ]
    (h : IsToppedSplitForcingSystem θ P R π E t) :
    IsToppedSplitForcingSystem (woodinSourceIndex θ) (woodinInsertSeed θ P {∅})
      (woodinInsertSeed θ R (({∅} : V) ×ˢ {∅})) (woodinSeedProjections θ P π)
      (woodinSeedSections θ E t) (woodinInsertSeed θ t ∅) := by
  constructor
  · intro i hi
    rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
    · rw [woodinInsertSeed_zero, woodinInsertSeed_zero, woodinInsertSeed_zero]
      exact singletonForcing_top ∅
    · rw [woodinInsertSeed_at_sourceIndex ha, woodinInsertSeed_at_sourceIndex ha,
        woodinInsertSeed_at_sourceIndex ha]
      exact h.top a ha
  · intro i hi j hj hij
    let := IsOrdinal.of_mem hj
    rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
    · rw [woodinSeedProjections_zero_value hj (woodinSeed_top_mem (fun a ha ↦ (h.top a ha).1) j hj),
        woodinInsertSeed_zero]
    · let := IsOrdinal.of_mem ha
      have hjn := woodinSourceIndex_subset_nonzero hij
      have hrj := (woodinRecursiveIndex_mem_iff hjn).mpr hj
      rw [woodinSeedProjections, woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr ha) hj
        (woodinSourceIndex_nonzero a), woodinRecursiveIndex_sourceIndex,
        woodinInsertSeed_at_sourceIndex ha, woodinInsertSeed_nonzero hj hjn]
      exact h.projTop a ha _ hrj (woodinSourceIndex_subset_recursive hij)
  · intro i hi j hj hij
    let := IsOrdinal.of_mem hj
    rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
    · rw [woodinInsertSeed_zero, woodinSeedSections_zero_value hj]
    · let := IsOrdinal.of_mem ha
      have hjn := woodinSourceIndex_subset_nonzero hij
      have hrj := (woodinRecursiveIndex_mem_iff hjn).mpr hj
      rw [woodinSeedSections, woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr ha) hj
        (woodinSourceIndex_nonzero a), woodinRecursiveIndex_sourceIndex,
        woodinInsertSeed_at_sourceIndex ha, woodinInsertSeed_nonzero hj hjn]
      exact h.secTop a ha _ hrj (woodinSourceIndex_subset_recursive hij)

theorem woodinSeed_split {θ P R π E t : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (ht : IsToppedSplitForcingSystem θ P R π E t) :
    IsSplitForcingSystem (woodinSourceIndex θ) (woodinInsertSeed θ P {∅})
      (woodinSeedProjections θ P π) (woodinSeedSections θ E t) := by
  have htm : ∀ a ∈ θ, t ‘ a ∈ P ‘ a := fun a ha ↦ (ht.top a ha).1
  refine ⟨woodinSeed_projMaps h, woodinSeed_secMaps h htm, ?_, ?_, ?_, ?_⟩
  · intro i hi p hp
    rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
    · rw [woodinInsertSeed_zero] at hp
      have he := mem_singleton_iff.mp hp
      subst p
      rw [woodinSeedSections_zero_value hi, woodinInsertSeed_zero]
    · rw [woodinInsertSeed_at_sourceIndex ha] at hp
      rw [woodinSeedSections, woodinSeedMatrix_at_sourceIndex ha ha]
      exact h.secId a ha p hp
  · intro i hi j hj k hk hij hjk p hp
    let := IsOrdinal.of_mem hj
    let := IsOrdinal.of_mem hk
    rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
    · rw [woodinSeedProjections_zero_value hj (woodinSeed_projMaps h j hj k hk hjk p hp),
        woodinSeedProjections_zero_value hk hp]
    · let := IsOrdinal.of_mem ha
      have hjn := woodinSourceIndex_subset_nonzero hij
      have hik : woodinSourceIndex a ⊆ k := fun x hx ↦ hjk x (hij x hx)
      have hkn := woodinSourceIndex_subset_nonzero hik
      have hrj := (woodinRecursiveIndex_mem_iff hjn).mpr hj
      have hrk := (woodinRecursiveIndex_mem_iff hkn).mpr hk
      have hrecjk : woodinRecursiveIndex j ⊆ woodinRecursiveIndex k :=
        woodinSourceIndex_subset_iff.mp (by
          simpa only [woodinSourceIndex_recursiveIndex j hjn,
            woodinSourceIndex_recursiveIndex k hkn] using hjk)
      rw [woodinInsertSeed_nonzero hk hkn] at hp
      rw [woodinSeedProjections, woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr ha) hj
        (woodinSourceIndex_nonzero a), woodinSeedMatrix_positive hj hk hjn,
        woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr ha) hk (woodinSourceIndex_nonzero a),
        woodinRecursiveIndex_sourceIndex]
      exact h.projComp a ha _ hrj _ hrk (woodinSourceIndex_subset_recursive hij) hrecjk p hp
  · intro i hi j hj k hk hij hjk p hp
    let := IsOrdinal.of_mem hj
    let := IsOrdinal.of_mem hk
    rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
    · rw [woodinInsertSeed_zero] at hp
      have he := mem_singleton_iff.mp hp
      subst p
      rw [woodinSeedSections_zero_value hj, woodinSeedSections_zero_value hk]
      exact (woodinSeed_tops ht).secTop j hj k hk hjk
    · let := IsOrdinal.of_mem ha
      have hjn := woodinSourceIndex_subset_nonzero hij
      have hik : woodinSourceIndex a ⊆ k := fun x hx ↦ hjk x (hij x hx)
      have hkn := woodinSourceIndex_subset_nonzero hik
      have hrj := (woodinRecursiveIndex_mem_iff hjn).mpr hj
      have hrk := (woodinRecursiveIndex_mem_iff hkn).mpr hk
      have hrecjk : woodinRecursiveIndex j ⊆ woodinRecursiveIndex k :=
        woodinSourceIndex_subset_iff.mp (by
          simpa only [woodinSourceIndex_recursiveIndex j hjn,
            woodinSourceIndex_recursiveIndex k hkn] using hjk)
      rw [woodinInsertSeed_at_sourceIndex ha] at hp
      rw [woodinSeedSections, woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr ha) hj
        (woodinSourceIndex_nonzero a), woodinSeedMatrix_positive hj hk hjn,
        woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr ha) hk (woodinSourceIndex_nonzero a),
        woodinRecursiveIndex_sourceIndex]
      exact h.secComp a ha _ hrj _ hrk (woodinSourceIndex_subset_recursive hij) hrecjk p hp
  · intro i hi j hj hij p hp
    let := IsOrdinal.of_mem hj
    rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
    · rw [woodinInsertSeed_zero] at hp
      have he := mem_singleton_iff.mp hp
      subst p
      rw [woodinSeedSections_zero_value hj,
        woodinSeedProjections_zero_value hj (woodinSeed_top_mem htm j hj)]
    · let := IsOrdinal.of_mem ha
      have hjn := woodinSourceIndex_subset_nonzero hij
      have hrj := (woodinRecursiveIndex_mem_iff hjn).mpr hj
      rw [woodinInsertSeed_at_sourceIndex ha] at hp
      rw [woodinSeedProjections, woodinSeedSections,
        woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr ha) hj (woodinSourceIndex_nonzero a),
        woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr ha) hj (woodinSourceIndex_nonzero a),
        woodinRecursiveIndex_sourceIndex]
      exact h.retraction a ha _ hrj (woodinSourceIndex_subset_recursive hij) p hp

end ZFVP
