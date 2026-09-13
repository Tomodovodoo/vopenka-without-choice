import ZFVP.ModelTheory.WoodinStageNameCoding
import ZFVP.ModelTheory.WoodinEndpointModel
import ZFVP.ModelTheory.WoodinStageRankAgreement
import ZFVP.ModelTheory.ForcingLowRankNames

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace WoodinEndpointModel
variable {δ : V} (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) {G : Set V}
  (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ δ)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec δ))) ‘ δ) G)

noncomputable def localNameValue (τ : ForcingName (woodinStageCarrier δ)) :
    (context hδ hAC hG).Model :=
  (context hδ hAC hG).ofName ⟨nameAction (woodinStageMap δ) τ.val,
    nameAction_isName (woodinStageMap_endpoint_maps hδ hAC) τ.property⟩

theorem localNameValue_mem_rank (τ : ForcingName (woodinStageCarrier δ))
    (hτ : τ.val ∈ hierarchy δ) :
    localNameValue hδ hAC hG τ ∈ hierarchy ((context hδ hAC hG).check δ) := by
  let := hδ.inaccessible.1
  exact (context hδ hAC hG).ofName_nameAction_mem_hierarchy
    (woodinStageMap_endpoint_maps hδ hAC) τ.property hτ

/-- The endpoint rank is exactly the values of the local presentation's
ground names lying below the endpoint. -/
theorem mem_rank_iff_localName (x : (context hδ hAC hG).Model) :
    x ∈ hierarchy ((context hδ hAC hG).check δ) ↔
      ∃ τ : ForcingName (woodinStageCarrier δ), τ.val ∈ hierarchy δ ∧ x = localNameValue hδ hAC hG τ := by
  let := hδ.inaccessible.1
  let B := context hδ hAC hG
  constructor
  · intro hx
    obtain ⟨β, hβ, hβx⟩ := (B.mem_check_iff δ (rank x)).mp
      ((mem_hierarchy_iff_rank_mem x (B.check δ)).mp hx)
    let := IsOrdinal.of_mem hβ
    let i := succ β
    have hi : i ∈ δ := regularCardinal_succ_closed hδ.inaccessible.regular hβ
    have hi' : i ∈ succ δ := mem_succ_iff.mpr (Or.inr hi)
    have hv := (woodinIteration_endpoint_valid hδ hAC).1
    let P := (forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ i
    let R := (forcingCodeR (kpair.π₁ (woodinIterationRec δ))) ‘ i
    let t := (forcingCodet (kpair.π₁ (woodinIterationRec δ))) ‘ i
    let π := (forcingCodeπ (kpair.π₁ (woodinIterationRec δ))) ‘ ⟨i, δ⟩ₖ
    let E := (forcingCodeE (kpair.π₁ (woodinIterationRec δ))) ‘ ⟨i, δ⟩ₖ
    have hR : IsForcingPreorder P R := hv.code.system.order.preorder i hi'
    have ht : IsForcingTop P R t := hv.code.system.tops.top i hi'
    have hπ : IsForcingSplitProjection P R B.P B.R π E :=
      hv.code.system.splitProjection hi' (mem_succ_self δ) (IsOrdinal.toIsTransitive.transitive _ hi)
    let A : ForcingContext V := ⟨P, R, t, forcingProjectionGeneric P R π B.G,
      hR, ht, hπ.projection.generic hR B.generic⟩
    let j := A.projectionInclusion B hπ rfl
    have heq : j (hierarchy (A.check i)) = hierarchy (B.check i) :=
      woodinIteration_endpoint_projection_rankAgreement hδ hAC hi A B
        rfl rfl rfl rfl rfl rfl hπ rfl
    have hxi : x ∈ hierarchy (B.check i) := by
      apply (mem_hierarchy_iff_rank_mem _ _).mpr
      rw [hβx]
      exact (B.check_mem_iff _ _).mpr (mem_succ_self β)
    obtain ⟨y, hy, hxy⟩ := j.endExtension (hierarchy (A.check i)) x (heq.symm ▸ hxi)
    have hsub : A.check i ⊆ A.check δ := (A.checkEmbedding.subset_iff i δ).mpr
      (IsOrdinal.toIsTransitive.transitive _ hi)
    have hyδ : y ∈ hierarchy (A.check δ) := hierarchy_mono hsub y hy
    obtain ⟨τ, hτδ, hyτ⟩ := (A.mem_checked_hierarchy_iff_low_name_of_inaccessible hδ.inaccessible
      (woodinIteration_endpoint_earlier_poset_small hδ hAC hi) y).mp hyδ
    let σ : ForcingName (woodinStageCarrier δ) := ⟨nameAction (woodinStageTag δ i) τ.val,
      nameAction_isName (woodinStageTag_maps hδ hAC hi) τ.property⟩
    refine ⟨σ, woodinStageTag_name_mem_hierarchy hδ hAC hi τ.property hτδ, ?_⟩
    change x = B.ofName ⟨nameAction (woodinStageMap δ) (nameAction (woodinStageTag δ i) τ.val), _⟩
    simp only [nameAction_compose (woodinStageTag_maps hδ hAC hi)
      (woodinStageMap_endpoint_maps hδ hAC) τ.property, woodinStageTag_compose_endpoint hδ hAC hi]
    rw [A.projectionInclusion_nameAction B hπ rfl τ]
    exact hxy.trans (congrArg j hyτ)
  · rintro ⟨τ, hτ, rfl⟩
    exact localNameValue_mem_rank hδ hAC hG τ hτ

end WoodinEndpointModel
end ZFVP
