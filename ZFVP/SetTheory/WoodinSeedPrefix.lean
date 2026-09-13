import ZFVP.SetTheory.WoodinSeedSupport

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinInsertSeed_prefix_value {θ α f a j : V} [IsOrdinal θ] [IsOrdinal α]
    (hα : α ⊆ θ) (hj : j ∈ woodinSourceIndex α) :
    (woodinInsertSeed θ f a) ‘ j = (woodinInsertSeed α f a) ‘ j := by
  have hjθ := woodinSourceIndex_subset_iff.mpr hα j hj
  by_cases hz : j = ∅
  · subst j
    rw [woodinInsertSeed_zero, woodinInsertSeed_zero]
  · rw [woodinInsertSeed_nonzero hjθ hz, woodinInsertSeed_nonzero hj hz]

theorem woodinSeedSections_prefix_value {θ α E t i j : V} [IsOrdinal θ] [IsOrdinal α]
    (hα : α ⊆ θ) (hi : i ∈ woodinSourceIndex α) (hj : j ∈ woodinSourceIndex α) :
    (woodinSeedSections θ E t) ‘ ⟨i, j⟩ₖ = (woodinSeedSections α E t) ‘ ⟨i, j⟩ₖ := by
  have hiθ := woodinSourceIndex_subset_iff.mpr hα i hi
  have hjθ := woodinSourceIndex_subset_iff.mpr hα j hj
  unfold woodinSeedSections
  by_cases hz : i = ∅
  · subst i
    rw [woodinSeedMatrix_zero hjθ, woodinSeedMatrix_zero hj,
      woodinSeedSectionColumn, value_definableGraph _ _ _ hjθ,
      woodinSeedSectionColumn, value_definableGraph _ _ _ hj,
      woodinInsertSeed_prefix_value hα hj]
  · rw [woodinSeedMatrix_positive hiθ hjθ hz, woodinSeedMatrix_positive hi hj hz]

theorem woodinSeedProjections_prefix_value {θ α P π i j : V} [IsOrdinal θ] [IsOrdinal α]
    (hα : α ⊆ θ) (hi : i ∈ woodinSourceIndex α) (hj : j ∈ woodinSourceIndex α) :
    (woodinSeedProjections θ P π) ‘ ⟨i, j⟩ₖ = (woodinSeedProjections α P π) ‘ ⟨i, j⟩ₖ := by
  have hiθ := woodinSourceIndex_subset_iff.mpr hα i hi
  have hjθ := woodinSourceIndex_subset_iff.mpr hα j hj
  unfold woodinSeedProjections
  by_cases hz : i = ∅
  · subst i
    rw [woodinSeedMatrix_zero hjθ, woodinSeedMatrix_zero hj,
      woodinSeedProjectionColumn, value_definableGraph _ _ _ hjθ,
      woodinSeedProjectionColumn, value_definableGraph _ _ _ hj,
      woodinInsertSeed_prefix_value hα hj]
  · rw [woodinSeedMatrix_positive hiθ hjθ hz, woodinSeedMatrix_positive hi hj hz]

theorem woodinSeed_prefix_support_iff {θ α E t f k : V} [IsOrdinal θ] [IsOrdinal α]
    [IsFunction f] (hf : domain f = θ) (hα : α ⊆ θ) :
    IsThreadSupport (woodinSourceIndex α) (woodinSeedSections θ E t)
      ((woodinInsertSeed θ f ∅) ↾ (woodinSourceIndex α)) k ↔
    IsThreadSupport (woodinSourceIndex α) (woodinSeedSections α E t)
      (woodinInsertSeed α (f ↾ α) ∅) k := by
  rw [← woodinInsertSeed_restrict hf hα]
  constructor
  · rintro ⟨hk, hs⟩
    refine ⟨hk, ?_⟩
    intro j hj hkj
    rw [← woodinSeedSections_prefix_value hα hk hj]
    exact hs j hj hkj
  · rintro ⟨hk, hs⟩
    refine ⟨hk, ?_⟩
    intro j hj hkj
    rw [woodinSeedSections_prefix_value hα hk hj]
    exact hs j hj hkj

theorem woodinSeed_inherited_support_iff {θ α E t f : V} [IsOrdinal θ] [IsOrdinal α]
    [IsFunction f] (hf : domain f = θ) (hα : α ⊆ θ) (hzero : (∅ : V) ∈ α)
    (ht : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → (E ‘ ⟨i, j⟩ₖ) ‘ (t ‘ i) = t ‘ j) :
    (∃ k, IsThreadSupport (woodinSourceIndex α) (woodinSeedSections θ E t)
      ((woodinInsertSeed θ f ∅) ↾ (woodinSourceIndex α)) k) ↔
    ∃ k, IsThreadSupport α E (f ↾ α) k := by
  simp_rw [woodinSeed_prefix_support_iff hf hα]
  exact woodinSeed_support_exists_iff hzero
    (fun i hi j hj hij ↦ ht i (hα i hi) j (hα j hj) hij)

end ZFVP
