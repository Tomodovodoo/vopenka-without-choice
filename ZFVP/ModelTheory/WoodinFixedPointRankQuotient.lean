import ZFVP.ModelTheory.WoodinFixedPointLowNames
import ZFVP.ModelTheory.ForcingPullbackRealization
import ZFVP.ModelTheory.ForcingRankTruth

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace WoodinEndpointModel
variable {δ γ : V} (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) {G : Set V}
  (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ δ)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec δ))) ‘ δ) G)
  (hγ : γ ∈ δ) (hfix : (kpair.π₂ (woodinIterationRec δ)) ‘ γ = γ)

noncomputable def fixedPointLocalContext : ForcingContext V :=
  (stageContext hδ hAC hG hγ).pullbackContext (woodinStageMap_fixedPoint_maps hδ hAC hγ hfix)
    (fun _ hp ↦ woodinStageMap_fixedPoint_surjective hδ hAC hγ hfix hp)

theorem fixedPointLocalContext_order :
    (fixedPointLocalContext hδ hAC hG hγ hfix).R = woodinLocalOrderOn (woodinStageCarrier γ) :=
  (woodinLocalOrderOn_fixedPoint_pullback hδ hAC hγ hfix).symm

noncomputable def fixedPointLocalInclusion :
    MembershipEndExtension (fixedPointLocalContext hδ hAC hG hγ hfix).Model
      (stageContext hδ hAC hG hγ).Model :=
  (stageContext hδ hAC hG hγ).pullbackInclusion (woodinStageMap_fixedPoint_maps hδ hAC hγ hfix)
    (fun _ hp ↦ woodinStageMap_fixedPoint_surjective hδ hAC hγ hfix hp)

theorem fixedPointLocalInclusion_ofName (τ : ForcingName (woodinStageCarrier γ)) :
    fixedPointLocalInclusion hδ hAC hG hγ hfix ((fixedPointLocalContext hδ hAC hG hγ hfix).ofName τ) =
      fixedPointLocalNameValue hδ hAC hG hγ hfix τ :=
  (stageContext hδ hAC hG hγ).pullbackInclusion_ofName (woodinStageMap_fixedPoint_maps hδ hAC hγ hfix)
    (fun _ hp ↦ woodinStageMap_fixedPoint_surjective hδ hAC hγ hfix hp) τ

/-- Local forcing names in the ground rank, identified by actual generic equality. -/
abbrev FixedPointLowNameQuotient :=
  ClassForcingQuotient (fixedPointLocalContext hδ hAC hG hγ hfix).P
    (fixedPointLocalContext hδ hAC hG hγ hfix).R (fixedPointLocalContext hδ hAC hG hγ hfix).G
    (fixedPointLocalContext hδ hAC hG hγ hfix).order (fixedPointLocalContext hδ hAC hG hγ hfix).generic.1
    (IsLowRankForcingName (woodinStageCarrier γ) γ) (fun _ h ↦ h.2)

instance fixedPointLowNameQuotient_setStructure :
    SetStructure (FixedPointLowNameQuotient hδ hAC hG hγ hfix) where
  mem y x := x.val ∈ y.val

noncomputable def fixedPointLowNameToStageRank (x : FixedPointLowNameQuotient hδ hAC hG hγ hfix) :
    SetDomain (hierarchy ((stageContext hδ hAC hG hγ).check γ)) :=
  ⟨fixedPointLocalInclusion hδ hAC hG hγ hfix x.val, by
    obtain ⟨τ, hτ, hx⟩ := x.property
    change x.val = (fixedPointLocalContext hδ hAC hG hγ hfix).ofName ⟨τ, hτ.2⟩ at hx
    have hn : IsForcingName (woodinStageCarrier γ) τ := hτ.2
    rw [hx]
    exact (fixedPointLocalInclusion_ofName hδ hAC hG hγ hfix ⟨τ, hn⟩).symm ▸
      fixedPointLocalNameValue_mem_rank hδ hAC hG hγ hfix ⟨τ, hn⟩ hτ.1⟩

theorem fixedPointLowNameToStageRank_bijective :
    Function.Bijective (fixedPointLowNameToStageRank hδ hAC hG hγ hfix) := by
  constructor
  · intro x y h
    exact Subtype.ext ((fixedPointLocalInclusion hδ hAC hG hγ hfix).injective (congrArg Subtype.val h))
  · intro x
    obtain ⟨τ, hτ, hx⟩ := (fixedPoint_mem_rank_iff_localName hδ hAC hG hγ hfix x.val).mp x.property
    let y : FixedPointLowNameQuotient hδ hAC hG hγ hfix :=
      ⟨(fixedPointLocalContext hδ hAC hG hγ hfix).ofName τ, τ.val, ⟨hτ, τ.property⟩, rfl⟩
    refine ⟨y, Subtype.ext ?_⟩
    exact (fixedPointLocalInclusion_ofName hδ hAC hG hγ hfix τ).trans hx.symm

noncomputable def fixedPointLowNameStageRankEquiv :
    FixedPointLowNameQuotient hδ hAC hG hγ hfix ≃
      SetDomain (hierarchy ((stageContext hδ hAC hG hγ).check γ)) :=
  Equiv.ofBijective (fixedPointLowNameToStageRank hδ hAC hG hγ hfix)
    (fixedPointLowNameToStageRank_bijective hδ hAC hG hγ hfix)

theorem fixedPointLowNameStageRankEquiv_mem_iff (x y : FixedPointLowNameQuotient hδ hAC hG hγ hfix) :
    fixedPointLowNameStageRankEquiv hδ hAC hG hγ hfix x ∈
      fixedPointLowNameStageRankEquiv hδ hAC hG hγ hfix y ↔ x ∈ y :=
  (fixedPointLocalInclusion hδ hAC hG hγ hfix).mem_iff x.val y.val

/-- Ground-rank local names at a fixed point give exactly the endpoint rank. -/
noncomputable def fixedPointLowNameRankEquiv : FixedPointLowNameQuotient hδ hAC hG hγ hfix ≃
    SetDomain (hierarchy ((context hδ hAC hG).check γ)) :=
  (fixedPointLowNameStageRankEquiv hδ hAC hG hγ hfix).trans (stageRankEquiv hδ hAC hG hγ)

theorem fixedPointLowNameRankEquiv_mem_iff (x y : FixedPointLowNameQuotient hδ hAC hG hγ hfix) :
    fixedPointLowNameRankEquiv hδ hAC hG hγ hfix x ∈
      fixedPointLowNameRankEquiv hδ hAC hG hγ hfix y ↔ x ∈ y :=
  (stageRankEquiv_mem_iff hδ hAC hG hγ _ _).trans
    (fixedPointLowNameStageRankEquiv_mem_iff hδ hAC hG hγ hfix x y)

instance fixedPointLowNameQuotient_nonempty : Nonempty (FixedPointLowNameQuotient hδ hAC hG hγ hfix) := by
  let := fixedPointRank_nonempty hδ hAC hG hγ hfix
  exact Nonempty.map (fixedPointLowNameRankEquiv hδ hAC hG hγ hfix).symm inferInstance

theorem fixedPointLowNameQuotient_models_zfc :
    (FixedPointLowNameQuotient hδ hAC hG hγ hfix)↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖 := by
  let := fixedPointRank_nonempty hδ hAC hG hγ hfix
  let := fixedPointRank_models_zfc hδ hAC hG hγ hfix
  constructor
  intro φ hφ
  apply (eval_membershipIso (fixedPointLowNameRankEquiv hδ hAC hG hγ hfix)
    (fixedPointLowNameRankEquiv_mem_iff hδ hAC hG hγ hfix) φ ![] Empty.elim).mpr
  have hs := Theory.models (SetDomain (hierarchy ((context hδ hAC hG).check γ))) 𝗭𝗙𝗖 hφ
  change φ.Eval ![] Empty.elim at hs
  have hf : (fixedPointLowNameRankEquiv hδ hAC hG hγ hfix) ∘
      (Empty.elim : Empty → FixedPointLowNameQuotient hδ hAC hG hγ hfix) = Empty.elim :=
    funext fun x ↦ Empty.elim x
  simpa only [hf, Matrix.empty_eq] using hs

end WoodinEndpointModel
end ZFVP
