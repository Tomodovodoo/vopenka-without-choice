import ZFVP.ModelTheory.WoodinSparseFixedPointInclusion
import ZFVP.ModelTheory.TwoStepInclusion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω γ δ : V} [IsOrdinal Ω] [IsOrdinal γ] [IsOrdinal δ]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) {G : Set V}
  (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G)
  (hγ : γ ∈ Ω) (hδ : δ ∈ Ω) (hγδ : γ ∈ δ)
local notation "A" => woodinSparseFixedPointContext hΩ hAC hG hγ
local notation "B" => woodinSparseFixedPointContext hΩ hAC hG hδ
local notation "π" => (forcingCodeπ (woodinSparseStageCode δ)) ‘ ⟨γ, δ⟩ₖ

include hγδ in
theorem woodinSparseFixedPointContext_between_retraction :
    IsForcingRetraction (A).P (A).R (B).P (B).R π :=
  woodinSparseStage_retraction_to_row hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hδ) hγδ

include hγδ in
theorem woodinSparseFixedPointContext_between_generic_iff (p : V) :
    p ∈ (A).G ↔ p ∈ (B).G ∧ p ∈ (A).P := by
  have hsub := (woodinSparseFixedPointContext_between_retraction hΩ hAC hG hγ hδ hγδ).inclusion
  rw [woodinSparseFixedPointContext_generic_iff hΩ hAC hG hγ,
    woodinSparseFixedPointContext_generic_iff hΩ hAC hG hδ]
  exact ⟨fun h ↦ ⟨⟨h.1, hsub p h.2⟩, h.2⟩, fun h ↦ ⟨h.1.1, h.2⟩⟩

noncomputable def woodinSparseFixedPointContext_between : MembershipEndExtension (A).Model (B).Model :=
  ForcingContext.retractionEmbedding (A) (B)
    (woodinSparseFixedPointContext_between_retraction hΩ hAC hG hγ hδ hγδ)
    (woodinSparseFixedPointContext_between_generic_iff hΩ hAC hG hγ hδ hγδ)

theorem woodinSparseFixedPointContext_between_check (x : V) :
    woodinSparseFixedPointContext_between hΩ hAC hG hγ hδ hγδ ((A).check x) = (B).check x :=
  ForcingContext.retractionInclusion_check (A) (B)
    (woodinSparseFixedPointContext_between_retraction hΩ hAC hG hγ hδ hγδ)
    (woodinSparseFixedPointContext_between_generic_iff hΩ hAC hG hγ hδ hγδ)
    ((woodinSparseFixedPointContext_top hΩ hAC hG hγ).trans
      (woodinSparseFixedPointContext_top hΩ hAC hG hδ).symm) x

theorem woodinSparseFixedPointContext_inclusion_between (x : (A).Model) :
    woodinSparseFixedPointContext_inclusion hΩ hAC hG hδ
      (woodinSparseFixedPointContext_between hΩ hAC hG hγ hδ hγδ x) =
        woodinSparseFixedPointContext_inclusion hΩ hAC hG hγ x := by
  apply (A).endExtension_ext
    ((woodinSparseFixedPointContext_inclusion hΩ hAC hG hδ).comp
      (woodinSparseFixedPointContext_between hΩ hAC hG hγ hδ hγδ))
    (woodinSparseFixedPointContext_inclusion hΩ hAC hG hγ)
  intro u
  change woodinSparseFixedPointContext_inclusion hΩ hAC hG hδ
      (woodinSparseFixedPointContext_between hΩ hAC hG hγ hδ hγδ ((A).check u)) =
    woodinSparseFixedPointContext_inclusion hΩ hAC hG hγ ((A).check u)
  rw [woodinSparseFixedPointContext_between_check,
    woodinSparseFixedPointContext_inclusion_check, woodinSparseFixedPointContext_inclusion_check]

end ZFVP
