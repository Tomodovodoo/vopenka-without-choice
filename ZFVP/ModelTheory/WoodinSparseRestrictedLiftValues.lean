import ZFVP.ModelTheory.WoodinSparseEndpointOrdinals

/-! Images of checked ordinals under the lift, computed inside the endpoint rank. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω γ δ e : V} [IsOrdinal Ω] [IsOrdinal γ] [IsOrdinal δ]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) {G : Set V}
  (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G)
  (hγ : γ ∈ Ω) (hδ : δ ∈ Ω) (hγδ : γ ∈ δ)
  (hfixγ : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ)
  (hfixδ : (kpair.π₂ (woodinIterationRec Ω)) ‘ δ = δ)
  (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd γ (ω : V)))
    (hierarchy (ordinalAdd δ (ω : V))) e)
  (hP : e ‘ (woodinSparseFixedPointContext hΩ hAC hG hγ).P =
    (woodinSparseFixedPointContext hΩ hAC hG hδ).P)
  (hg : ∀ p ∈ (woodinSparseFixedPointContext hΩ hAC hG hγ).G,
    e ‘ p ∈ (woodinSparseFixedPointContext hΩ hAC hG hδ).G)
local notation "E" => woodinSparseGenericContext hΩ hAC (subset_refl Ω) hG

theorem woodinSparseRestrictedLiftRankGraph_checkedOrdinal {α β : V}
    [IsOrdinal α] [IsOrdinal β] (hαγ : α ∈ γ) (hβΩ : β ∈ Ω) (himage : e ‘ α = β) :
    (woodinSparseRestrictedLiftRankGraph hΩ hAC hG hγ hδ hγδ hfixγ hfixδ he hP hg) ‘
      (WoodinSparseEndpointModel.checkedOrdinal hΩ hAC hG
        (IsOrdinal.toIsTransitive.mem_trans hαγ hγ)) =
      WoodinSparseEndpointModel.checkedOrdinal hΩ hAC hG hβΩ := by
  let := hierarchy_transitive ((E).check Ω)
  apply Subtype.ext
  change (MembershipEndExtension.transitiveSubtype (hierarchy ((E).check Ω))) (_ ‘ _) = _
  rw [(MembershipEndExtension.transitiveSubtype (hierarchy ((E).check Ω))).map_value_total]
  change (woodinSparseRestrictedLiftGraph hΩ hAC hG hγ hδ hγδ hfixγ hfixδ he hP hg) ‘
    ((E).check α) = (E).check β
  rw [woodinSparseRestrictedLiftGraph_check hΩ hAC hG hγ hδ hγδ hfixγ hfixδ he hP hg
    (ordinal_subset_hierarchy γ α hαγ), himage]

end ZFVP
