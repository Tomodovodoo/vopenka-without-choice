import ZFVP.SetTheory.CnExtendibleSmallEmbedding

/-! One family of small embeddings works at every level below the one it was produced at.

The last two paragraphs of the paper's finite restoration theorem: the witnesses given by the
Bagaria-Poveda criterion at the top level `N` also witness the criterion at each level `m ≤ N`,
so the same cardinals are `C(m+1)`-extendible for every such `m`, unboundedly. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The criterion at a higher level implies the criterion at a lower one: the same stages and the
same embeddings work, since `C(n+1)` is contained in `C(m+1)` for `m ≤ n`. -/
theorem SmallEmbeddingCriterion.of_le {m n : ℕ} {δ : V} (hmn : m ≤ n)
    (h : SmallEmbeddingCriterion (n + 1) δ) : SmallEmbeddingCriterion (m + 1) δ := by
  intro η hη
  obtain ⟨θ, hηθ, hθ, hall⟩ := h η hη
  refine ⟨θ, hηθ, hθ.of_le (by omega), ?_⟩
  intro α hα
  obtain ⟨δ', θ', α', e, h1, h2, h3, hθ', h5, h6, h7, h8⟩ := hall α hα
  exact ⟨δ', θ', α', e, h1, h2, h3, hθ'.of_le (by omega), h5, h6, h7, h8⟩

theorem IsCnExtendible.of_smallEmbeddingCriterion_le {m n : ℕ} {δ : V} (hmn : m ≤ n)
    (hδ : IsInitialOrdinal δ) (h : SmallEmbeddingCriterion (n + 1) δ) :
    IsCnExtendible (m + 1) δ :=
  IsCnExtendible.of_smallEmbeddingCriterion hδ (h.of_le hmn)

/-- The paper's conclusion: one unbounded supply of criterion witnesses at level `N` gives
unboundedly many `C(m+1)`-extendible cardinals for every `m ≤ N`. -/
theorem cnExtendible_unbounded_of_smallEmbeddingCriterion {n : ℕ}
    (h : ∀ η : V, IsOrdinal η →
      ∃ δ : V, η ∈ δ ∧ IsInitialOrdinal δ ∧ SmallEmbeddingCriterion (n + 1) δ)
    {m : ℕ} (hmn : m ≤ n) :
    ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsCnExtendible (m + 1) κ := by
  intro α hα
  obtain ⟨δ, hαδ, hδ, hcrit⟩ := h α hα
  exact ⟨δ, hαδ, IsCnExtendible.of_smallEmbeddingCriterion_le hmn hδ hcrit⟩

/-- The same statement with the level written as `N ≥ 1`, for the finite restoration caller. -/
theorem cnExtendible_unbounded_of_smallEmbeddingCriterion' {N : ℕ} (hN : 1 ≤ N)
    (h : ∀ η : V, IsOrdinal η →
      ∃ δ : V, η ∈ δ ∧ IsInitialOrdinal δ ∧ SmallEmbeddingCriterion N δ) :
    ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsCnExtendible N κ := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact cnExtendible_unbounded_of_smallEmbeddingCriterion h (le_refl m)

end ZFVP
