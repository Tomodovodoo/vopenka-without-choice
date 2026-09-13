import ZFVP.ModelTheory.WoodinFixedPointRank
import ZFVP.ModelTheory.WoodinEndpointModel

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace WoodinEndpointModel
variable {δ γ : V} (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) {G : Set V}
  (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ δ)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec δ))) ‘ δ) G)
  (hγ : γ ∈ δ)

noncomputable def stageContext : ForcingContext V := by
  let := hδ.inaccessible.1
  let h := (woodinIteration_endpoint_valid hδ hAC).1.code.system
  let hi := mem_succ_iff.mpr (Or.inr hγ)
  let P := (forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ γ
  let R := (forcingCodeR (kpair.π₁ (woodinIterationRec δ))) ‘ γ
  let π := (forcingCodeπ (kpair.π₁ (woodinIterationRec δ))) ‘ ⟨γ, δ⟩ₖ
  exact ⟨P, R, (forcingCodet (kpair.π₁ (woodinIterationRec δ))) ‘ γ,
    forcingProjectionGeneric P R π G, h.order.preorder γ hi, h.tops.top γ hi,
    (h.splitProjection hi (mem_succ_self δ) (IsOrdinal.toIsTransitive.transitive _ hγ)).projection.generic
      (h.order.preorder γ hi) hG⟩

theorem stage_splitProjection : IsForcingSplitProjection
    (stageContext hδ hAC hG hγ).P (stageContext hδ hAC hG hγ).R
    (context hδ hAC hG).P (context hδ hAC hG).R
    ((forcingCodeπ (kpair.π₁ (woodinIterationRec δ))) ‘ ⟨γ, δ⟩ₖ)
    ((forcingCodeE (kpair.π₁ (woodinIterationRec δ))) ‘ ⟨γ, δ⟩ₖ) := by
  let := hδ.inaccessible.1
  exact (woodinIteration_endpoint_valid hδ hAC).1.code.system.splitProjection
    (mem_succ_iff.mpr (Or.inr hγ)) (mem_succ_self δ) (IsOrdinal.toIsTransitive.transitive _ hγ)

noncomputable def stageInclusion :
    MembershipEndExtension (stageContext hδ hAC hG hγ).Model (context hδ hAC hG).Model :=
  (stageContext hδ hAC hG hγ).projectionInclusion (context hδ hAC hG)
    (stage_splitProjection hδ hAC hG hγ) rfl

theorem stageInclusion_hierarchy :
    stageInclusion hδ hAC hG hγ (hierarchy ((stageContext hδ hAC hG hγ).check γ)) =
      hierarchy ((context hδ hAC hG).check γ) :=
  woodinIteration_endpoint_projection_rankAgreement hδ hAC hγ
    (stageContext hδ hAC hG hγ) (context hδ hAC hG)
    rfl rfl rfl rfl rfl rfl (stage_splitProjection hδ hAC hG hγ) rfl

noncomputable def stageRankMap :
    SetDomain (hierarchy ((stageContext hδ hAC hG hγ).check γ)) →
      SetDomain (hierarchy ((context hδ hAC hG).check γ)) :=
  fun x ↦ ⟨stageInclusion hδ hAC hG hγ x.val, by
    rw [← stageInclusion_hierarchy hδ hAC hG hγ]
    exact ((stageInclusion hδ hAC hG hγ).mem_iff _ _).mpr x.property⟩

theorem stageRankMap_bijective : Function.Bijective (stageRankMap hδ hAC hG hγ) := by
  constructor
  · intro x y h
    exact Subtype.ext ((stageInclusion hδ hAC hG hγ).injective (congrArg Subtype.val h))
  · intro y
    have hy : y.val ∈ stageInclusion hδ hAC hG hγ
        (hierarchy ((stageContext hδ hAC hG hγ).check γ)) :=
      (congrArg (fun z ↦ y.val ∈ z) (stageInclusion_hierarchy hδ hAC hG hγ)).mpr y.property
    obtain ⟨x, hx, he⟩ := (stageInclusion hδ hAC hG hγ).endExtension _ y.val hy
    exact ⟨⟨x, hx⟩, Subtype.ext he.symm⟩

/-- The projection inclusion identifies the stage rank with the same rank in
the full endpoint extension. No supercompactness of the stage is required. -/
noncomputable def stageRankEquiv :
    SetDomain (hierarchy ((stageContext hδ hAC hG hγ).check γ)) ≃
      SetDomain (hierarchy ((context hδ hAC hG).check γ)) :=
  Equiv.ofBijective (stageRankMap hδ hAC hG hγ) (stageRankMap_bijective hδ hAC hG hγ)

theorem stageRankEquiv_mem_iff
    (x y : SetDomain (hierarchy ((stageContext hδ hAC hG hγ).check γ))) :
    stageRankEquiv hδ hAC hG hγ x ∈ stageRankEquiv hδ hAC hG hγ y ↔ x ∈ y :=
  (stageInclusion hδ hAC hG hγ).mem_iff x.val y.val

include hγ

theorem fixedPointRank_nonempty
    (hfix : (kpair.π₂ (woodinIterationRec δ)) ‘ γ = γ) :
    Nonempty (SetDomain (hierarchy ((context hδ hAC hG).check γ))) := by
  let := (stageContext hδ hAC hG hγ).woodinFixedPoint_rank_nonempty hδ hAC
    (mem_succ_iff.mpr (Or.inr hγ)) hfix rfl rfl rfl
  exact Nonempty.map (stageRankEquiv hδ hAC hG hγ) inferInstance

/-- Every fixed-point rank below the construction endpoint satisfies ZFC in
the actual full generic extension. -/
theorem fixedPointRank_models_zfc
    (hfix : (kpair.π₂ (woodinIterationRec δ)) ‘ γ = γ)
    [Nonempty (SetDomain (hierarchy ((context hδ hAC hG).check γ)))] :
    (SetDomain (hierarchy ((context hδ hAC hG).check γ)))↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖 := by
  let A := stageContext hδ hAC hG hγ
  let := A.woodinFixedPoint_rank_nonempty hδ hAC
    (mem_succ_iff.mpr (Or.inr hγ)) hfix rfl rfl rfl
  let := A.woodinFixedPoint_rank_models_zfc hδ hAC
    (mem_succ_iff.mpr (Or.inr hγ)) hfix rfl rfl rfl
  constructor
  intro φ hφ
  have hs := Theory.models (SetDomain (hierarchy (A.check γ))) 𝗭𝗙𝗖 hφ
  change φ.Eval ![] Empty.elim at hs
  have he := (eval_membershipIso (stageRankEquiv hδ hAC hG hγ)
    (stageRankEquiv_mem_iff hδ hAC hG hγ) φ ![] Empty.elim).mp hs
  have hf : (fun x : Empty ↦ stageRankEquiv hδ hAC hG hγ (Empty.elim x)) = Empty.elim :=
    funext fun x ↦ Empty.elim x
  simpa only [models_iff, Semiformula.Realize, Function.comp_def, Matrix.empty_eq, hf] using he

end WoodinEndpointModel
end ZFVP
