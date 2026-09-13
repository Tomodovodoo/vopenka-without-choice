import ZFVP.ModelTheory.WoodinSparseFiniteTruthWindow
import ZFVP.ModelTheory.WoodinSparseConsistencyPassage

/-! Finite restoration with the actual forcing correctness window discharged.
The only remaining hypothesis is relative homogeneity of the actual sparse
endpoint forcing over its supercompact stages.
-/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory Entailment

local notation "P[" θ "]" => (forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ)
local notation "R[" θ "]" => (forcingCodeR (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ)
local notation "π[" i "," θ "]" => (forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex θ⟩ₖ

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

/-- The fixed Sat dictionary determines the ground level; its actual window
supplies correctness of every reflected stage inside the endpoint model. -/
theorem prunedUE_sparseEndpoint_cnExtendible_unbounded_of_relativeHomogeneity
    (hhom : ∀ δ ∈ Λ, IsWoodinSupercompact δ →
      ∀ t ∈ P[Λ], ∀ p ∈ P[Λ], ⟨π[δ,Λ] ‘ p, π[δ,Λ] ‘ t⟩ₖ ∈ R[δ] →
        ∃ a, IsForcingAutomorphism P[Λ] R[Λ] a ∧
          (∀ q ∈ P[Λ], π[δ,Λ] ‘ (a ‘ q) = π[δ,Λ] ‘ q) ∧
          ForcingCompatible P[Λ] R[Λ] (a ‘ p) t) :
    ∀ η : WoodinSparseEndpointModel.RankModel (woodinSparse_restorationFacts hΛ).2.2 hAC hG,
      IsOrdinal η →
        ∃ δ : WoodinSparseEndpointModel.RankModel (woodinSparse_restorationFacts hΛ).2.2 hAC hG,
          η ∈ δ ∧ IsCnExtendible (k + 1) δ := by
  apply prunedUE_sparseEndpoint_cnExtendible_unbounded_of_forcing hΛ hAC hG ?_ hhom
  intro θ hθΛ hθ hθW
  let := hθ.ordinal
  exact woodinSparse_cn_window (woodinSparse_restorationFacts hΛ).2.2 hθW hAC hG hθΛ
    (k + 1) (woodinSparse_restorationFacts hΛ).2.1 hθ

end Endpoint

variable
  (hhom : ∀ (M : Type) [SetStructure M] [Nonempty M] [Countable M]
    [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [M↓[ℒₛₑₜ] ⊧* zfUEVPNoRankBerkeleyTheory]
    (Λ : M), IsWoodinSupercompact Λ → ¬InternalChoice M →
    ∀ δ ∈ Λ, IsWoodinSupercompact δ →
      ∀ t ∈ P[Λ], ∀ p ∈ P[Λ], ⟨π[δ,Λ] ‘ p, π[δ,Λ] ‘ t⟩ₖ ∈ R[δ] →
        ∃ a, IsForcingAutomorphism P[Λ] R[Λ] a ∧
          (∀ q ∈ P[Λ], π[δ,Λ] ‘ (a ‘ q) = π[δ,Λ] ‘ q) ∧
          ForcingCompatible P[Λ] R[Λ] (a ‘ p) t)

include hhom

/-- The actual generic construction supplies finite restoration; only the
displayed relative homogeneity statement is supplied from outside this proof. -/
theorem finiteRestorationInput_of_sparseRelativeHomogeneity : FiniteRestorationInput := by
  apply finiteRestorationInput_of_sparseForcing (fun k ↦ woodinSparseSatLevel (k + 1))
  · intro M _ _ _ _ _ k Λ _ hΛ hAC G hG θ hθΛ hθ hθW
    let := hθ.ordinal
    exact woodinSparse_cn_window (woodinSparse_restorationFacts hΛ).2.2 hθW hAC hG hθΛ
      (k + 1) (woodinSparse_restorationFacts hΛ).2.1 hθ
  · intro M _ _ _ _ _ k Λ hΛ hAC
    exact hhom M Λ (woodinSparse_restorationFacts hΛ).2.2 hAC

theorem finite_subset_zfcVP_models_of_sparseRelativeHomogeneity (h : Consistent zfVPTheory)
    (u : Finset SetTheorySentence) (hu : ↑u ⊆ zfcVPTheory) :
    ∃ (W : Type) (_ : Nonempty W) (_ : Structure ℒₛₑₜ W), W↓[ℒₛₑₜ] ⊧* (u : Theory ℒₛₑₜ) :=
  finite_subset_zfcVP_models (finiteRestorationInput_of_sparseRelativeHomogeneity hhom) h u hu

theorem consistent_zfcVP_iff_consistent_zfVP_of_sparseRelativeHomogeneity :
    Consistent zfcVPTheory ↔ Consistent zfVPTheory :=
  consistent_zfcVP_iff_consistent_zfVP (finiteRestorationInput_of_sparseRelativeHomogeneity hhom)

end ZFVP
