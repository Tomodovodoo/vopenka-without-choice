import ZFVP.ModelTheory.WoodinSparseConditionalRestoration
import ZFVP.ModelTheory.ConsistencyTransferPassage

/-! The actual sparse endpoint construction feeds the effective finite-model
and compactness arguments. Correctness preservation and actual relative
homogeneity remain explicit here until their forcing proofs are supplied.
-/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory Entailment

local notation "P[" θ "]" => (forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ)
local notation "R[" θ "]" => (forcingCodeR (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ)
local notation "π[" i "," θ "]" => (forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex θ⟩ₖ

variable (r : ℕ → ℕ)
  (hcorrect : ∀ (M : Type) [SetStructure M] [Nonempty M] [Countable M]
    [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [M↓[ℒₛₑₜ] ⊧* zfUEVPNoRankBerkeleyTheory]
    (k : ℕ) (Λ : M) [IsOrdinal Λ]
    (hΛ : IsCnExtendible (woodinSparseFiniteRestorationLevel (r k)) Λ)
    (hAC : ¬InternalChoice M) (G : Set M)
    (hG : IsExternalForcingGeneric
      ((forcingCodeP (kpair.π₁ (woodinIterationRec Λ))) ‘ Λ)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec Λ))) ‘ Λ) G),
    ∀ (θ : M) (hθΛ : θ ∈ Λ) (hθ : Cn (r k) θ), IsWoodinSupercompact θ →
      letI := hθ.ordinal
      Cn (k + 2) (WoodinSparseEndpointModel.checkedOrdinal
        (woodinSparse_restorationFacts hΛ).2.2 hAC hG hθΛ))
  (hhom : ∀ (M : Type) [SetStructure M] [Nonempty M] [Countable M]
    [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [M↓[ℒₛₑₜ] ⊧* zfUEVPNoRankBerkeleyTheory]
    (k : ℕ) (Λ : M), IsCnExtendible (woodinSparseFiniteRestorationLevel (r k)) Λ →
    ¬InternalChoice M →
    ∀ δ ∈ Λ, IsWoodinSupercompact δ →
      ∀ t ∈ P[Λ], ∀ p ∈ P[Λ], ⟨π[δ,Λ] ‘ p, π[δ,Λ] ‘ t⟩ₖ ∈ R[δ] →
        ∃ a, IsForcingAutomorphism P[Λ] R[Λ] a ∧
          (∀ q ∈ P[Λ], π[δ,Λ] ‘ (a ‘ q) = π[δ,Λ] ‘ q) ∧
          ForcingCompatible P[Λ] R[Λ] (a ‘ p) t)

include r hcorrect hhom

/-- The abstract compactness input is obtained from an actual generic of the
selected Woodin iteration and its actual sparse endpoint rank. -/
theorem finiteRestorationInput_of_sparseForcing : FiniteRestorationInput := by
  intro M hstr hne hcnt hM hAC N hN
  let iMs := hstr
  let iMn := hne
  let iMc := hcnt
  let iMu := hM
  let iMzf : M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := prunedUEVP_models_zf M
  cases N with
  | zero => omega
  | succ k =>
    obtain ⟨Λ, hΛ, G, hG, _, _, hZFC⟩ :=
      prunedUE_exists_sparseUniformRestorationGeneric (r k) hAC (∅ : M) inferInstance
    let := hΛ.1.1
    let W := WoodinSparseEndpointModel.RankModel (woodinSparse_restorationFacts hΛ).2.2 hAC hG
    refine ⟨W, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
    · exact ⟨fun _ hφ ↦ hZFC.models_set (Or.inr hφ)⟩
    · exact prunedUE_sparseEndpoint_cnExtendible_unbounded_of_forcing hΛ hAC hG
        (hcorrect M k Λ hΛ hAC G hG) (hhom M k Λ hΛ hAC)

/-- Every finite subset is modeled by the actual endpoint in the choiceless
case; its required extendibility level is computed from the input sentences. -/
theorem finite_subset_zfcVP_models_of_sparseForcing (h : Consistent zfVPTheory)
    (u : Finset SetTheorySentence) (hu : ↑u ⊆ zfcVPTheory) :
    ∃ (W : Type) (_ : Nonempty W) (_ : Structure ℒₛₑₜ W), W↓[ℒₛₑₜ] ⊧* (u : Theory ℒₛₑₜ) :=
  finite_subset_zfcVP_models (finiteRestorationInput_of_sparseForcing r hcorrect hhom) h u hu

/-- The consistency equivalence follows from the two concrete forcing facts
and the actual sparse endpoint construction. -/
theorem consistent_zfcVP_iff_consistent_zfVP_of_sparseForcing :
    Consistent zfcVPTheory ↔ Consistent zfVPTheory :=
  consistent_zfcVP_iff_consistent_zfVP (finiteRestorationInput_of_sparseForcing r hcorrect hhom)

end ZFVP
