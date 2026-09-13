import ZFVP.ModelTheory.WoodinSparseFiniteRestoration
import ZFVP.ModelTheory.WoodinSparseSourceRelativeHomogeneity

/-! Finite restoration and the consistency equivalence from the actual Woodin
iteration. The ground selection, generic, correctness window, relative
homogeneity, restricted lift, and internal small-embedding criterion are all
proved in the imported construction.
-/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory Entailment

section Endpoint
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable [V↓[ℒₛₑₜ] ⊧* unboundedExtendibilityTheory]
variable {k : ℕ} {Λ : V} [IsOrdinal Λ]
variable (hΛ : IsCnExtendible
    (woodinSparseFiniteRestorationLevel (woodinSparseSatLevel (k + 1))) Λ)
  (hAC : ¬InternalChoice V) {G : Set V}
  (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec Λ))) ‘ Λ)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec Λ))) ‘ Λ) G)

/-- The small-embedding witnesses, including each embedding graph, are elements
of the actual selected endpoint. -/
theorem prunedUE_sparseEndpoint_smallEmbedding_unbounded :
    ∀ η : WoodinSparseEndpointModel.RankModel (woodinSparse_restorationFacts hΛ).2.2 hAC hG,
      IsOrdinal η →
        ∃ δ : WoodinSparseEndpointModel.RankModel (woodinSparse_restorationFacts hΛ).2.2 hAC hG,
          η ∈ δ ∧ SmallEmbeddingCriterion (k + 1) δ := by
  apply prunedUE_sparseEndpoint_smallEmbedding_unbounded_of_forcing hΛ hAC hG ?_
    (woodinSparseSource_relative_homogeneity (woodinSparse_restorationFacts hΛ).2.2 hAC)
  intro θ hθΛ hθ hθW
  let := hθ.ordinal
  exact woodinSparse_cn_window (woodinSparse_restorationFacts hΛ).2.2 hθW hAC hG hθΛ
    (k + 1) (woodinSparse_restorationFacts hΛ).2.1 hθ

/-- The actual selected endpoint has unbounded C(k+1)-extendibles. -/
theorem prunedUE_sparseEndpoint_cnExtendible_unbounded :
    ∀ η : WoodinSparseEndpointModel.RankModel (woodinSparse_restorationFacts hΛ).2.2 hAC hG,
      IsOrdinal η →
        ∃ δ : WoodinSparseEndpointModel.RankModel (woodinSparse_restorationFacts hΛ).2.2 hAC hG,
          η ∈ δ ∧ IsCnExtendible (k + 1) δ :=
  prunedUE_sparseEndpoint_cnExtendible_unbounded_of_relativeHomogeneity hΛ hAC hG
    (woodinSparseSource_relative_homogeneity (woodinSparse_restorationFacts hΛ).2.2 hAC)

end Endpoint

/-- Finite restoration: every countable choiceless pruned ground has the
required ZFC model with unbounded C(N)-extendibles, for each positive N. -/
theorem finite_restoration : FiniteRestorationInput :=
  finiteRestorationInput_of_sparseRelativeHomogeneity
    (fun _ _ _ _ _ _ _ hΛ hAC ↦ woodinSparseSource_relative_homogeneity hΛ hAC)

/-- Every finite subset of ZFC+VP is satisfiable from consistency of ZF+VP.
The choiceless case uses the actual generic endpoint from finite restoration. -/
theorem finite_subset_zfcVP_models_woodin (h : Consistent zfVPTheory)
    (u : Finset SetTheorySentence) (hu : ↑u ⊆ zfcVPTheory) :
    ∃ (W : Type) (_ : Nonempty W) (_ : Structure ℒₛₑₜ W), W↓[ℒₛₑₜ] ⊧* (u : Theory ℒₛₑₜ) :=
  finite_subset_zfcVP_models finite_restoration h u hu

theorem consistent_zfcVP_of_consistent_zfVP_woodin (h : Consistent zfVPTheory) :
    Consistent zfcVPTheory :=
  consistent_zfcVP_of_consistent_zfVP finite_restoration h

/-- Con(ZFC+VP) if and only if Con(ZF+VP). -/
theorem consistent_zfcVP_iff_consistent_zfVP_woodin :
    Consistent zfcVPTheory ↔ Consistent zfVPTheory :=
  consistent_zfcVP_iff_consistent_zfVP finite_restoration

end ZFVP
