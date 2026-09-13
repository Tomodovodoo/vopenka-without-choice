import ZFVP.ModelTheory.WoodinSparseRestorationTheorem
import ZFVP.SetTheory.CnExtendibleAllLowerLevels

/-! A single actual endpoint restores all levels up to a prescribed finite
index. Its small-embedding graphs are quantified as elements of that endpoint.
The window may be any upper bound for the computed Sat level.
-/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable [V↓[ℒₛₑₜ] ⊧* unboundedExtendibilityTheory]

theorem prunedUE_sparseEndpoint_all_lower_extendibles {N r : ℕ} {Λ : V} [IsOrdinal Λ]
    (hr : woodinSparseSatLevel (N + 1) ≤ r)
    (hΛ : IsCnExtendible (woodinSparseFiniteRestorationLevel r) Λ)
    (hAC : ¬InternalChoice V) {G : Set V}
    (hG : IsExternalForcingGeneric
      ((forcingCodeP (kpair.π₁ (woodinIterationRec Λ))) ‘ Λ)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec Λ))) ‘ Λ) G) :
    ∀ η : WoodinSparseEndpointModel.RankModel (woodinSparse_restorationFacts hΛ).2.2 hAC hG,
      IsOrdinal η →
        ∃ δ : WoodinSparseEndpointModel.RankModel (woodinSparse_restorationFacts hΛ).2.2 hAC hG,
          η ∈ δ ∧ (∀ n ≤ N, IsCnExtendible n δ) ∧ SmallEmbeddingCriterion (N + 1) δ := by
  have hw := prunedUE_sparseEndpoint_smallEmbedding_unbounded_of_forcing
    (k := N) hΛ hAC hG (fun θ hθΛ hθ hθW ↦ by
      let := hθ.ordinal
      exact woodinSparse_cn_window (woodinSparse_restorationFacts hΛ).2.2 hθW hAC hG hθΛ
        (N + 1) ((woodinSparse_restorationFacts hΛ).2.1.of_le hr) (hθ.of_le hr))
    (woodinSparseSource_relative_homogeneity (woodinSparse_restorationFacts hΛ).2.2 hAC)
  intro η hη
  obtain ⟨δ, hηδ, hδ⟩ := hw η hη
  exact ⟨δ, hηδ, fun n hn ↦ hδ.cnExtendible.of_le_all (by omega) (by omega), hδ⟩

/-- A countable ZF+UE ground supplies the generic and endpoint; no external
well-foundedness or transitivity condition is imposed on the ground model. -/
theorem prunedUE_exists_sparseRestorationRange [Countable V] (N r : ℕ)
    (hr : woodinSparseSatLevel (N + 1) ≤ r)
    (hAC : ¬InternalChoice V) (α : V) (hα : IsOrdinal α) :
    ∃ (Λ : V) (hΛ : IsCnExtendible (woodinSparseFiniteRestorationLevel r) Λ)
      (G : Set V) (hG : IsExternalForcingGeneric
        ((forcingCodeP (kpair.π₁ (woodinIterationRec Λ))) ‘ Λ)
        ((forcingCodeR (kpair.π₁ (woodinIterationRec Λ))) ‘ Λ) G),
      α ∈ Λ ∧ (woodinSeedCardinal : V) ∈ Λ ∧
        letI : IsOrdinal Λ := hΛ.1.1
        let W := WoodinSparseEndpointModel.RankModel (woodinSparse_restorationFacts hΛ).2.2 hAC hG
        W↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖 ∧
          ∀ η : W, IsOrdinal η → ∃ δ : W,
            η ∈ δ ∧ (∀ n ≤ N, IsCnExtendible n δ) ∧ SmallEmbeddingCriterion (N + 1) δ := by
  obtain ⟨Λ, hΛ, G, hG, hαΛ, hseed, hZFC⟩ :=
    prunedUE_exists_sparseUniformRestorationGeneric r hAC α hα
  let := hΛ.1.1
  exact ⟨Λ, hΛ, G, hG, hαΛ, hseed, hZFC,
    prunedUE_sparseEndpoint_all_lower_extendibles hr hΛ hAC hG⟩

end ZFVP
