import ZFVP.ModelTheory.WoodinSparseRestrictedCriticalLift
import ZFVP.ModelTheory.WoodinSparseEndpointZFC
import ZFVP.ModelTheory.EndExtensionCodedEmbedding
import ZFVP.ModelTheory.TransitiveZFRankOperations

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω : V} [IsOrdinal Ω]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) {G : Set V}
  (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G)
local notation "E" => woodinSparseGenericContext hΩ hAC (subset_refl Ω) hG
local notation "W" => WoodinSparseEndpointModel.RankModel hΩ hAC hG

namespace WoodinSparseEndpointModel
noncomputable def checkedOrdinal {α : V} [IsOrdinal α] (hα : α ∈ Ω) : W :=
  ⟨(E).check α, ordinal_mem_hierarchy_iff.mpr (((E).check_mem_iff _ _).mpr hα)⟩

instance checkedOrdinal_isOrdinal {α : V} [IsOrdinal α] (hα : α ∈ Ω) :
    IsOrdinal (checkedOrdinal hΩ hAC hG hα) := by
  let := hierarchy_transitive ((E).check Ω)
  apply (TransitiveZF.ordinal_iff (hierarchy ((E).check Ω)) _).mpr
  change IsOrdinal ((E).check α)
  infer_instance
end WoodinSparseEndpointModel

variable {γ δ e : V} [IsOrdinal γ] [IsOrdinal δ]
variable (hγ : γ ∈ Ω) (hδ : δ ∈ Ω) (hγδ : γ ∈ δ)
  (hfixγ : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ)
  (hfixδ : (kpair.π₂ (woodinIterationRec Ω)) ‘ δ = δ)
  (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd γ (ω : V)))
    (hierarchy (ordinalAdd δ (ω : V))) e)
  (hP : e ‘ (woodinSparseFixedPointContext hΩ hAC hG hγ).P =
    (woodinSparseFixedPointContext hΩ hAC hG hδ).P)
  (hg : ∀ p ∈ (woodinSparseFixedPointContext hΩ hAC hG hγ).G,
    e ‘ p ∈ (woodinSparseFixedPointContext hΩ hAC hG hδ).G)

noncomputable def woodinSparseRestrictedLiftRankGraph : W :=
  ⟨woodinSparseRestrictedLiftGraph hΩ hAC hG hγ hδ hγδ hfixγ hfixδ he hP hg,
    woodinSparseRestrictedLiftGraph_mem hΩ hAC hG hγ hδ hγδ hfixγ hfixδ he hP hg⟩

theorem woodinSparseRestrictedLiftRankGraph_codedElementary :
    IsCodedMembershipEmbedding (hierarchy (WoodinSparseEndpointModel.checkedOrdinal hΩ hAC hG hγ))
      (hierarchy (WoodinSparseEndpointModel.checkedOrdinal hΩ hAC hG hδ))
      (woodinSparseRestrictedLiftRankGraph hΩ hAC hG hγ hδ hγδ hfixγ hfixδ he hP hg) := by
  let := hierarchy_transitive ((E).check Ω)
  apply (TransitiveZF.codedMembershipEmbedding_iff (hierarchy ((E).check Ω)) _ _ _).mp
  rw [rank_hierarchy_val _ inferInstance, rank_hierarchy_val _ inferInstance]
  exact woodinSparseRestrictedLiftGraph_codedElementary hΩ hAC hG hγ hδ hγδ hfixγ hfixδ he hP hg

theorem woodinSparseRestrictedLiftRankGraph_criticalPoint {κ : V} [IsOrdinal κ]
    (hκ : IsCriticalPoint (hierarchy (ordinalAdd γ (ω : V))) e κ) (hκγ : κ ∈ γ) :
    IsCriticalPoint (hierarchy (WoodinSparseEndpointModel.checkedOrdinal hΩ hAC hG hγ))
      (woodinSparseRestrictedLiftRankGraph hΩ hAC hG hγ hδ hγδ hfixγ hfixδ he hP hg)
      (WoodinSparseEndpointModel.checkedOrdinal hΩ hAC hG (IsOrdinal.toIsTransitive.mem_trans hκγ hγ)) := by
  let := hierarchy_transitive ((E).check Ω)
  let := hierarchy_transitive (WoodinSparseEndpointModel.checkedOrdinal hΩ hAC hG hγ)
  apply (MembershipEndExtension.transitiveSubtype (hierarchy ((E).check Ω))).criticalPoint_iff.mp
  change IsCriticalPoint (hierarchy (WoodinSparseEndpointModel.checkedOrdinal hΩ hAC hG hγ)).val
    _ ((E).check κ)
  rw [rank_hierarchy_val _ inferInstance]
  exact woodinSparseRestrictedLiftGraph_criticalPoint hΩ hAC hG hγ hδ hγδ hfixγ hfixδ he hP hg hκ hκγ

end ZFVP
