import ZFVP.ModelTheory.WoodinFixedPointStageMap
import ZFVP.ModelTheory.WoodinFixedPointModel
import ZFVP.ModelTheory.ForcingLowRankNames

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace WoodinEndpointModel
variable {δ γ : V} (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) {G : Set V}
  (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ δ)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec δ))) ‘ δ) G)
  (hγ : γ ∈ δ) (hfix : (kpair.π₂ (woodinIterationRec δ)) ‘ γ = γ)

noncomputable def fixedPointLocalNameValue (τ : ForcingName (woodinStageCarrier γ)) :
    (stageContext hδ hAC hG hγ).Model :=
  (stageContext hδ hAC hG hγ).ofName ⟨nameAction (woodinStageMap γ) τ.val,
    nameAction_isName (woodinStageMap_fixedPoint_maps hδ hAC hγ hfix) τ.property⟩

theorem fixedPointLocalNameValue_mem_rank (τ : ForcingName (woodinStageCarrier γ))
    (hτ : τ.val ∈ hierarchy γ) :
    fixedPointLocalNameValue hδ hAC hG hγ hfix τ ∈
      hierarchy ((stageContext hδ hAC hG hγ).check γ) := by
  let := (woodinIteration_fixedPoint_inaccessible hδ hAC hγ hfix).1
  exact (stageContext hδ hAC hG hγ).ofName_nameAction_mem_hierarchy
    (woodinStageMap_fixedPoint_maps hδ hAC hγ hfix) τ.property hτ

/-- The rank at a fixed point is represented by local names in the ground rank. -/
theorem fixedPoint_mem_rank_iff_localName (x : (stageContext hδ hAC hG hγ).Model) :
    x ∈ hierarchy ((stageContext hδ hAC hG hγ).check γ) ↔
      ∃ τ : ForcingName (woodinStageCarrier γ), τ.val ∈ hierarchy γ ∧
        x = fixedPointLocalNameValue hδ hAC hG hγ hfix τ := by
  let := hδ.inaccessible.1
  have hg := woodinIteration_fixedPoint_inaccessible hδ hAC hγ hfix
  let := hg.1
  let B := stageContext hδ hAC hG hγ
  constructor
  · intro hx
    obtain ⟨β, hβ, hβx⟩ := (B.mem_check_iff γ (rank x)).mp
      ((mem_hierarchy_iff_rank_mem x (B.check γ)).mp hx)
    let := IsOrdinal.of_mem hβ
    let i := succ β
    have hi : i ∈ γ := regularCardinal_succ_closed hg.regular hβ
    have hi' : i ∈ succ δ := mem_succ_iff.mpr (Or.inr (IsOrdinal.toIsTransitive.mem_trans hi hγ))
    have hγ' : γ ∈ succ δ := mem_succ_iff.mpr (Or.inr hγ)
    have hv := woodinIteration_endpoint_valid hδ hAC
    let P := (forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ i
    let R := (forcingCodeR (kpair.π₁ (woodinIterationRec δ))) ‘ i
    let t := (forcingCodet (kpair.π₁ (woodinIterationRec δ))) ‘ i
    let π := (forcingCodeπ (kpair.π₁ (woodinIterationRec δ))) ‘ ⟨i, γ⟩ₖ
    let E := (forcingCodeE (kpair.π₁ (woodinIterationRec δ))) ‘ ⟨i, γ⟩ₖ
    have hR : IsForcingPreorder P R := hv.1.code.system.order.preorder i hi'
    have ht : IsForcingTop P R t := hv.1.code.system.tops.top i hi'
    have hπ : IsForcingSplitProjection P R B.P B.R π E :=
      hv.1.code.system.splitProjection hi' hγ' (IsOrdinal.toIsTransitive.transitive _ hi)
    let A : ForcingContext V := ⟨P, R, t, forcingProjectionGeneric P R π B.G,
      hR, ht, hπ.projection.generic hR B.generic⟩
    let j := A.projectionInclusion B hπ rfl
    have heq : j (hierarchy (A.check i)) = hierarchy (B.check i) :=
      hv.1.projection_rankAgreement hv.2 hi' hγ' (IsOrdinal.toIsTransitive.transitive _ hi)
        (woodinIteration_endpoint_rankStage_at hδ hAC hi') A B rfl rfl rfl rfl rfl rfl hπ rfl
    have hxi : x ∈ hierarchy (B.check i) := by
      apply (mem_hierarchy_iff_rank_mem _ _).mpr
      rw [hβx]
      exact (B.check_mem_iff _ _).mpr (mem_succ_self β)
    obtain ⟨y, hy, hxy⟩ := j.endExtension (hierarchy (A.check i)) x (heq.symm ▸ hxi)
    have hsub : A.check i ⊆ A.check γ := (A.checkEmbedding.subset_iff i γ).mpr
      (IsOrdinal.toIsTransitive.transitive _ hi)
    have hyγ : y ∈ hierarchy (A.check γ) := hierarchy_mono hsub y hy
    obtain ⟨τ, hτγ, hyτ⟩ := (A.mem_checked_hierarchy_iff_low_name_of_inaccessible hg
      (woodinIteration_fixedPoint_earlier_poset_small hδ hAC hγ hfix hi) y).mp hyγ
    let σ : ForcingName (woodinStageCarrier γ) := ⟨nameAction (woodinStageTag δ i) τ.val,
      nameAction_isName (woodinStageTag_fixedPoint_maps hδ hAC hγ hfix hi) τ.property⟩
    refine ⟨σ, nameAction_mem_hierarchy_of_inaccessible hg
      (woodinIteration_fixedPoint_earlier_poset_small hδ hAC hγ hfix hi)
      (woodinStageTag_fixedPoint_mem_hierarchy hδ hAC hγ hfix hi) hτγ τ.property, ?_⟩
    change x = B.ofName ⟨nameAction (woodinStageMap γ) (nameAction (woodinStageTag δ i) τ.val), _⟩
    simp only [nameAction_compose (woodinStageTag_fixedPoint_maps hδ hAC hγ hfix hi)
      (woodinStageMap_fixedPoint_maps hδ hAC hγ hfix) τ.property,
      woodinStageTag_compose_fixedPoint hδ hAC hγ hfix hi]
    rw [A.projectionInclusion_nameAction B hπ rfl τ]
    exact hxy.trans (congrArg j hyτ)
  · rintro ⟨τ, hτ, rfl⟩
    exact fixedPointLocalNameValue_mem_rank hδ hAC hG hγ hfix τ hτ

end WoodinEndpointModel
end ZFVP
