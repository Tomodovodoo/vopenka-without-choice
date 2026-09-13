import ZFVP.ModelTheory.WoodinSparseRestorationEndpoint
import ZFVP.ModelTheory.UniformWoodinSparseCompleteCode
import ZFVP.ModelTheory.WoodinSparseCapturedProjection

/-! Finite restoration ground data for the fixed formula defining the actual
complete sparse code. Only the forcing-window level remains a variable.
-/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def woodinSparseFiniteRestorationLevel (r : ℕ) : ℕ :=
  woodinSparseRestorationLevel r woodinSparseCompleteStageCodeFormula

def woodinSparseFiniteWitnessLevel (r : ℕ) : ℕ :=
  woodinSparseWitnessLevel r woodinSparseCompleteStageCodeFormula

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Every supercompact stage selected for restoration is a fixed point of
the cardinal table at the same outer endpoint. -/
theorem woodinIteration_supercompact_fixedPoint {Λ θ : V}
    (hΛ : IsWoodinSupercompact Λ) (hθ : IsWoodinSupercompact θ)
    (hAC : ¬InternalChoice V) (hθΛ : θ ∈ Λ) :
    (kpair.π₂ (woodinIterationRec Λ)) ‘ θ = θ := by
  let := hθ.inaccessible.1
  exact (woodinIterationRec_cardinal_eq_endpoint hΛ hAC
    (mem_succ_iff.mpr (Or.inr hθΛ))).symm.trans (woodinIteration_endpoint_cardinal hθ hAC)

variable [V↓[ℒₛₑₜ] ⊧* unboundedExtendibilityTheory]

/-- The actual, fixed complete-code formula determines every reflection level
in this ground embedding family. There is no definability hypothesis. -/
theorem prunedUE_sparseUniformRestrictedStages {r : ℕ} {Λ η : V}
    (hΛ : IsCnExtendible (woodinSparseFiniteRestorationLevel r) Λ)
    (hAC : ¬InternalChoice V) (hη : η ∈ Λ) :
    ∃ δ : V, δ ∈ Λ ∧ η ∈ δ ∧ IsCnExtendible (woodinSparseFiniteWitnessLevel r) δ ∧
      Cn r δ ∧ IsWoodinSupercompact δ ∧
      ∀ β ∈ Λ, ∃ θ : V, θ ∈ Λ ∧ δ ∈ θ ∧ β ∈ θ ∧ Cn r θ ∧ IsWoodinSupercompact θ ∧
        ∀ α ∈ θ, ∃ e θ' α' J : V,
          η ∈ e ∧ e ∈ θ' ∧ θ' ∈ δ ∧ α' ∈ θ' ∧ Cn r θ' ∧ IsWoodinSupercompact θ' ∧
          IsCodedMembershipEmbedding (hierarchy (ordinalAdd θ' (ω : V)))
            (hierarchy (ordinalAdd θ (ω : V))) J ∧
          IsCriticalPoint (hierarchy (ordinalAdd θ' (ω : V))) J e ∧
          J ‘ e = δ ∧ J ‘ θ' = θ ∧ J ‘ α' = α ∧
          woodinSparseCompleteStageCode θ' ∈ hierarchy (ordinalAdd θ' (ω : V)) ∧
          J ‘ (woodinSparseCompleteStageCode θ') = woodinSparseCompleteStageCode θ :=
  prunedUE_sparseRestrictedStages hΛ eval_woodinSparseCompleteStageCodeFormula hAC hη

/-- Countability supplies a generic for the actual endpoint selected at the
explicit finite level derived from the fixed complete-code formula. -/
theorem prunedUE_exists_sparseUniformRestorationGeneric [Countable V] (r : ℕ)
    (hAC : ¬InternalChoice V) (α : V) (hα : IsOrdinal α) :
    ∃ (Λ : V) (hΛ : IsCnExtendible (woodinSparseFiniteRestorationLevel r) Λ)
      (G : Set V) (hG : IsExternalForcingGeneric
        ((forcingCodeP (kpair.π₁ (woodinIterationRec Λ))) ‘ Λ)
        ((forcingCodeR (kpair.π₁ (woodinIterationRec Λ))) ‘ Λ) G),
      α ∈ Λ ∧ (woodinSeedCardinal : V) ∈ Λ ∧
        letI : IsOrdinal Λ := hΛ.1.1
        (WoodinSparseEndpointModel.RankModel (woodinSparse_restorationFacts hΛ).2.2 hAC hG)↓[ℒₛₑₜ]
          ⊧* 𝗭𝗙𝗖 :=
  prunedUE_exists_sparseRestorationGeneric r woodinSparseCompleteStageCodeFormula hAC α hα

end ZFVP
