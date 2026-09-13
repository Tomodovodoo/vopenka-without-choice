import ZFVP.ModelTheory.WoodinSparseRankAgreement
import ZFVP.ModelTheory.EndExtensionBasics

/-! The actual sparse endpoint rank satisfies ZFC. The raw endpoint theorem
is transferred along the already constructed membership equivalence.
-/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace WoodinSparseEndpointModel
variable {Ω : V} [IsOrdinal Ω] (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
  {G : Set V} (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G)

local notation "Raw" => WoodinEndpointModel.context hΩ hAC hG
local notation "Sparse" => woodinSparseGenericContext hΩ hAC (subset_refl Ω) hG

abbrev RankModel := SetDomain (hierarchy ((Sparse).check Ω))

noncomputable def rankElementaryMap :
    ElementaryMap (WoodinEndpointModel.RankModel hΩ hAC hG) (RankModel hΩ hAC hG) := by
  let j := ElementaryMap.ofMembershipIso (woodinSparseEndpoint_rawEquiv hΩ hAC hG)
    (woodinSparseEndpoint_rawEquiv_mem hΩ hAC hG)
  have hheight : j (hierarchy ((Raw).check Ω)) = hierarchy ((Sparse).check Ω) :=
    (j.map_hierarchy ((Raw).check Ω)).trans
      (congrArg hierarchy (woodinSparseEndpoint_rawEquiv_check hΩ hAC hG Ω))
  have h := j.restrict (hierarchy ((Raw).check Ω))
  change ElementaryMap (WoodinEndpointModel.RankModel hΩ hAC hG)
    (SetDomain (j (hierarchy ((Raw).check Ω)))) at h
  rw [hheight] at h
  exact h

instance rankModel_nonempty : Nonempty (RankModel hΩ hAC hG) :=
  ⟨rankElementaryMap hΩ hAC hG (Classical.choice inferInstance)⟩

instance rankModel_models_zfc : (RankModel hΩ hAC hG)↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖 := by
  refine ⟨fun φ hφ ↦ ?_⟩
  exact ((rankElementaryMap hΩ hAC hG).models_sentence_iff φ).mp
    ((WoodinEndpointModel.rankModel_models_zfc hΩ hAC hG).models_set hφ)

instance rankModel_models_zf : (RankModel hΩ hAC hG)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 :=
  ⟨fun _ hφ ↦ (rankModel_models_zfc hΩ hAC hG).models_set (Or.inl hφ)⟩

end WoodinSparseEndpointModel
end ZFVP
