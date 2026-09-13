import ZFVP.ModelTheory.WoodinSparseRestorationLevelPrimrec
import ZFVP.ModelTheory.WoodinSparseSatLevelPrimrec
import ZFVP.ModelTheory.WoodinSparseFiniteRestorationRange

/-! The primitive-recursive finite-restoration index and its actual endpoint.
The ground assumptions are ZF, UE, and failure of Choice. The endpoint satisfies
ZFC, has unbounded extendibles at every level through N, and contains the lifted
small-embedding graphs.
-/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def woodinSparseRestorationWindow (N : ℕ) : ℕ :=
  woodinSparseSatLevelMajorant (N + 1)

/-- The finite index t_N, independent of the ground model and its endpoint. -/
def woodinSparseRestorationIndex (N : ℕ) : ℕ :=
  woodinSparseFiniteRestorationLevel (woodinSparseRestorationWindow N)

theorem woodinSparseRestorationWindow_primrec : Primrec woodinSparseRestorationWindow :=
  woodinSparseSatLevelMajorant_primrec.comp Primrec.succ

theorem woodinSparseRestorationIndex_primrec : Primrec woodinSparseRestorationIndex :=
  woodinSparseFiniteRestorationLevel_primrec.comp woodinSparseRestorationWindow_primrec

theorem woodinSparseRestorationWindow_bound (N : ℕ) :
    woodinSparseSatLevel (N + 1) ≤ woodinSparseRestorationWindow N :=
  woodinSparseSatLevel_le_majorant (N + 1)

theorem four_le_woodinSparseRestorationIndex (N : ℕ) :
    4 ≤ woodinSparseRestorationIndex N :=
  Nat.le_add_left 4 _

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable [V↓[ℒₛₑₜ] ⊧* unboundedExtendibilityTheory]

/-- Any selected E(t_N) endpoint and actual generic have all the required
restoration properties. The internal small-embedding criterion quantifies its
embedding graphs as elements of the displayed rank model. -/
theorem ue_woodinSparse_finiteRestoration {N : ℕ} {Λ : V} [IsOrdinal Λ]
    (hΛ : IsCnExtendible (woodinSparseRestorationIndex N) Λ)
    (hAC : ¬InternalChoice V) {G : Set V}
    (hG : IsExternalForcingGeneric
      ((forcingCodeP (kpair.π₁ (woodinIterationRec Λ))) ‘ Λ)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec Λ))) ‘ Λ) G) :
    let W := WoodinSparseEndpointModel.RankModel (woodinSparse_restorationFacts hΛ).2.2 hAC hG
    W↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖 ∧
      ∀ η : W, IsOrdinal η → ∃ δ : W,
        η ∈ δ ∧ (∀ n ≤ N, IsCnExtendible n δ) ∧ SmallEmbeddingCriterion (N + 1) δ :=
  ⟨WoodinSparseEndpointModel.rankModel_models_zfc (woodinSparse_restorationFacts hΛ).2.2 hAC hG,
    prunedUE_sparseEndpoint_all_lower_extendibles (woodinSparseRestorationWindow_bound N) hΛ hAC hG⟩

/-- A countable, possibly ill-founded ZF+UE ground constructs the endpoint and
its generic above any prescribed ground ordinal. -/
theorem ue_exists_woodinSparse_finiteRestoration [Countable V] (N : ℕ)
    (hAC : ¬InternalChoice V) (α : V) (hα : IsOrdinal α) :
    ∃ (Λ : V) (hΛ : IsCnExtendible (woodinSparseRestorationIndex N) Λ)
      (G : Set V) (hG : IsExternalForcingGeneric
        ((forcingCodeP (kpair.π₁ (woodinIterationRec Λ))) ‘ Λ)
        ((forcingCodeR (kpair.π₁ (woodinIterationRec Λ))) ‘ Λ) G),
      α ∈ Λ ∧ (woodinSeedCardinal : V) ∈ Λ ∧
        letI : IsOrdinal Λ := hΛ.1.1
        let W := WoodinSparseEndpointModel.RankModel (woodinSparse_restorationFacts hΛ).2.2 hAC hG
        W↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖 ∧
          ∀ η : W, IsOrdinal η → ∃ δ : W,
            η ∈ δ ∧ (∀ n ≤ N, IsCnExtendible n δ) ∧ SmallEmbeddingCriterion (N + 1) δ :=
  prunedUE_exists_sparseRestorationRange N (woodinSparseRestorationWindow N)
    (woodinSparseRestorationWindow_bound N) hAC α hα

end ZFVP
