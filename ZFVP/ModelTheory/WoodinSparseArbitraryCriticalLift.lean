import ZFVP.ModelTheory.WoodinSparseArbitraryEndpointLift

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω γ δ e κ : V} [IsOrdinal Ω] [IsOrdinal γ] [IsOrdinal δ]
local notation "Pγ" => (forcingCodeP (woodinSparseStageCode γ)) ‘ γ
local notation "Rγ" => (forcingCodeR (woodinSparseStageCode γ)) ‘ γ
local notation "Pδ" => (forcingCodeP (woodinSparseStageCode δ)) ‘ δ
local notation "Rδ" => (forcingCodeR (woodinSparseStageCode δ)) ‘ δ
local notation "πγ" => (forcingCodeπ (woodinSparseStageCode Ω)) ‘ ⟨γ, Ω⟩ₖ
local notation "πδ" => (forcingCodeπ (woodinSparseStageCode Ω)) ‘ ⟨δ, Ω⟩ₖ

theorem ForcingContext.woodinSparseEndpoint_exists_restricted_criticalLift
    (A : ForcingContext V) (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
    (hAP : A.P = (forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω)
    (hAR : A.R = (forcingCodeR (woodinSparseStageCode Ω)) ‘ Ω) (hone : A.one = ∅)
    (hγ : γ ∈ Ω) (hδ : δ ∈ Ω) (hγδ : γ ∈ δ)
    (hfixγ : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ)
    (hfixδ : (kpair.π₂ (woodinIterationRec Ω)) ‘ δ = δ)
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd γ (ω : V)))
      (hierarchy (ordinalAdd δ (ω : V))) e)
    (hP : e ‘ Pγ = Pδ)
    (hg : ∀ p ∈ forcingProjectionGeneric Pγ Rγ πγ A.G,
      e ‘ p ∈ forcingProjectionGeneric Pδ Rδ πδ A.G)
    (hκ : IsCriticalPoint (hierarchy (ordinalAdd γ (ω : V))) e κ) (hκγ : κ ∈ γ) :
    ∃ g ∈ hierarchy (A.check Ω),
      IsCodedMembershipEmbedding (hierarchy (A.check γ)) (hierarchy (A.check δ)) g ∧
      IsCriticalPoint (hierarchy (A.check γ)) g (A.check κ) ∧
      ∀ x ∈ hierarchy γ, g ‘ (A.check x) = A.check (e ‘ x) := by
  obtain ⟨G, hG, rfl⟩ := woodinSparseEndpoint_raw_generic_presentation hΩ hAC A hAP hAR hone
  have hprojγ : forcingProjectionGeneric Pγ Rγ πγ
      (woodinSparseGenericContext hΩ hAC (subset_refl Ω) hG).G =
        (woodinSparseFixedPointContext hΩ hAC hG hγ).G :=
    woodinSparseFixedPointContext_projectedGeneric hΩ hAC hG hγ
  have hprojδ : forcingProjectionGeneric Pδ Rδ πδ
      (woodinSparseGenericContext hΩ hAC (subset_refl Ω) hG).G =
        (woodinSparseFixedPointContext hΩ hAC hG hδ).G :=
    woodinSparseFixedPointContext_projectedGeneric hΩ hAC hG hδ
  have hg' : ∀ p ∈ (woodinSparseFixedPointContext hΩ hAC hG hγ).G,
      e ‘ p ∈ (woodinSparseFixedPointContext hΩ hAC hG hδ).G := by
    simpa only [hprojγ, hprojδ] using hg
  refine ⟨woodinSparseRestrictedLiftGraph hΩ hAC hG hγ hδ hγδ hfixγ hfixδ he hP hg',
    woodinSparseRestrictedLiftGraph_mem hΩ hAC hG hγ hδ hγδ hfixγ hfixδ he hP hg',
    woodinSparseRestrictedLiftGraph_codedElementary hΩ hAC hG hγ hδ hγδ hfixγ hfixδ he hP hg',
    woodinSparseRestrictedLiftGraph_criticalPoint hΩ hAC hG hγ hδ hγδ hfixγ hfixδ he hP hg' hκ hκγ, ?_⟩
  intro x hx
  exact woodinSparseRestrictedLiftGraph_check hΩ hAC hG hγ hδ hγδ hfixγ hfixδ he hP hg' hx

end ZFVP
