import ZFVP.ModelTheory.WoodinSparseGenericProjection
import ZFVP.ModelTheory.WoodinSparseLowNames

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingRetraction.projectedGeneric_iff {P R Q S π p : V}
    (h : IsForcingRetraction P R Q S π) (hR : IsForcingPreorder P R)
    {G : Set V} (hG : IsExternalForcingFilter Q S G) :
    p ∈ forcingProjectionGeneric P R π G ↔ p ∈ G ∧ p ∈ P := by
  constructor
  · rintro ⟨hp, q, hq, hqp⟩
    exact ⟨hG.2.2.1 q hq p (h.inclusion p hp) ((h.below q (hG.1 q hq) p hp).mpr hqp), hp⟩
  · rintro ⟨hpG, hp⟩
    exact ⟨hp, p, hpG, (h.fixes p hp).symm ▸ hR.2.1 p hp⟩

variable {Ω γ : V} [IsOrdinal Ω] [IsOrdinal γ]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) {G : Set V}
  (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G)
  (hγ : γ ∈ Ω)
local notation "A" => woodinSparseFixedPointContext hΩ hAC hG hγ
local notation "E" => woodinSparseGenericContext hΩ hAC (subset_refl Ω) hG
local notation "π" => (forcingCodeπ (woodinSparseStageCode Ω)) ‘ ⟨γ, Ω⟩ₖ

theorem woodinSparseFixedPointContext_projectedGeneric :
    forcingProjectionGeneric (A).P (A).R π (E).G = (A).G := by
  rw [woodinSparseGenericContext_generic]
  change forcingProjectionGeneric (A).P (A).R π (woodinSparseGeneric Ω G) =
    (woodinSparseGenericContext hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hγ)
      (woodinFixedPoint_stage_generic hΩ hAC hG hγ)).G
  rw [woodinSparseGenericContext_generic]
  have hh := woodinSparseGeneric_projected hΩ hAC (subset_refl Ω) hγ hG.1
  change forcingProjectionGeneric ((forcingCodeP (woodinSparseStageCode γ)) ‘ γ)
    ((forcingCodeR (woodinSparseStageCode γ)) ‘ γ) π (woodinSparseGeneric Ω G) = _
  rw [← hh]
  apply congrArg (woodinSparseGeneric γ)
  change forcingProjectionGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec γ))) ‘ γ)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec γ))) ‘ γ)
    ((forcingCodeπ (kpair.π₁ (woodinIterationRec Ω))) ‘ ⟨γ, Ω⟩ₖ) G =
      forcingProjectionGeneric
        ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ γ)
        ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ γ)
        ((forcingCodeπ (kpair.π₁ (woodinIterationRec Ω))) ‘ ⟨γ, Ω⟩ₖ) G
  rw [(woodinIterationStage_old_row hΩ hAC (subset_refl Ω) hγ).1,
    (woodinIterationStage_old_row hΩ hAC (subset_refl Ω) hγ).2]

theorem woodinSparseFixedPointContext_retraction :
    IsForcingRetraction (A).P (A).R (E).P (E).R π :=
  woodinSparseStage_retraction_to_row hΩ hAC (subset_refl Ω) hγ

theorem woodinSparseFixedPointContext_generic_iff (p : V) :
    p ∈ (A).G ↔ p ∈ (E).G ∧ p ∈ (A).P := by
  rw [← woodinSparseFixedPointContext_projectedGeneric hΩ hAC hG hγ]
  exact (woodinSparseFixedPointContext_retraction hΩ hAC hG hγ).projectedGeneric_iff (A).order (E).generic.1

theorem woodinSparseFixedPointContext_top : (A).one = ∅ :=
  woodinSparseGenericContext_top hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hγ)
    (woodinFixedPoint_stage_generic hΩ hAC hG hγ)

noncomputable def woodinSparseFixedPointContext_inclusion : MembershipEndExtension (A).Model (E).Model :=
  ForcingContext.retractionEmbedding (A) (E)
    (woodinSparseFixedPointContext_retraction hΩ hAC hG hγ)
    (woodinSparseFixedPointContext_generic_iff hΩ hAC hG hγ)

theorem woodinSparseFixedPointContext_inclusion_check (x : V) :
    woodinSparseFixedPointContext_inclusion hΩ hAC hG hγ ((A).check x) = (E).check x :=
  ForcingContext.retractionInclusion_check (A) (E)
    (woodinSparseFixedPointContext_retraction hΩ hAC hG hγ)
    (woodinSparseFixedPointContext_generic_iff hΩ hAC hG hγ)
    ((woodinSparseFixedPointContext_top hΩ hAC hG hγ).trans
      (woodinSparseGenericContext_top hΩ hAC (subset_refl Ω) hG).symm) x

end ZFVP
