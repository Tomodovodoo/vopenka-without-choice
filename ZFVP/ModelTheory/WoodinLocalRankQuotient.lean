import ZFVP.ModelTheory.WoodinEndpointLowNames
import ZFVP.ModelTheory.ForcingPullbackRealization
import ZFVP.ModelTheory.ForcingRankTruth
import ZFVP.SetTheory.MembershipIso

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace WoodinEndpointModel
variable {δ : V} (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) {G : Set V}
  (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ δ)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec δ))) ‘ δ) G)

noncomputable def localContext : ForcingContext V :=
  (context hδ hAC hG).pullbackContext (woodinStageMap_endpoint_maps hδ hAC)
    (fun _ hp ↦ woodinStageMap_endpoint_surjective hδ hAC hp)

theorem localContext_order :
    (localContext hδ hAC hG).R = woodinLocalOrderOn (woodinStageCarrier δ) :=
  (woodinLocalOrderOn_endpoint_pullback hδ hAC).symm

noncomputable def localInclusion :
    MembershipEndExtension (localContext hδ hAC hG).Model (context hδ hAC hG).Model :=
  (context hδ hAC hG).pullbackInclusion (woodinStageMap_endpoint_maps hδ hAC)
    (fun _ hp ↦ woodinStageMap_endpoint_surjective hδ hAC hp)

theorem localInclusion_ofName (τ : ForcingName (woodinStageCarrier δ)) :
    localInclusion hδ hAC hG ((localContext hδ hAC hG).ofName τ) =
      localNameValue hδ hAC hG τ :=
  (context hδ hAC hG).pullbackInclusion_ofName (woodinStageMap_endpoint_maps hδ hAC)
    (fun _ hp ↦ woodinStageMap_endpoint_surjective hδ hAC hp) τ

abbrev LowNameQuotient :=
  ClassForcingQuotient (localContext hδ hAC hG).P (localContext hδ hAC hG).R
    (localContext hδ hAC hG).G (localContext hδ hAC hG).order
    (localContext hδ hAC hG).generic.1 (IsLowRankForcingName (woodinStageCarrier δ) δ)
    (fun _ h ↦ h.2)

instance lowNameQuotient_setStructure : SetStructure (LowNameQuotient hδ hAC hG) where
  mem y x := x.val ∈ y.val

noncomputable def lowNameToRank (x : LowNameQuotient hδ hAC hG) : RankModel hδ hAC hG :=
  ⟨localInclusion hδ hAC hG x.val, by
    obtain ⟨τ, hτ, hx⟩ := x.property
    change x.val = (localContext hδ hAC hG).ofName ⟨τ, hτ.2⟩ at hx
    have hn : IsForcingName (woodinStageCarrier δ) τ := hτ.2
    rw [hx]
    exact (localInclusion_ofName hδ hAC hG ⟨τ, hn⟩).symm ▸
      localNameValue_mem_rank hδ hAC hG ⟨τ, hn⟩ hτ.1⟩

theorem lowNameToRank_injective : Function.Injective (lowNameToRank hδ hAC hG) := by
  intro x y h
  exact Subtype.ext ((localInclusion hδ hAC hG).injective (congrArg Subtype.val h))

theorem lowNameToRank_surjective : Function.Surjective (lowNameToRank hδ hAC hG) := by
  intro x
  obtain ⟨τ, hτ, hx⟩ := (mem_rank_iff_localName hδ hAC hG x.val).mp x.property
  let y : LowNameQuotient hδ hAC hG :=
    ⟨(localContext hδ hAC hG).ofName τ, τ.val, ⟨hτ, τ.property⟩, rfl⟩
  refine ⟨y, Subtype.ext ?_⟩
  exact (localInclusion_ofName hδ hAC hG τ).trans hx.symm

/-- The quotient of local names below the endpoint is the endpoint rank segment. -/
noncomputable def lowNameRankEquiv : LowNameQuotient hδ hAC hG ≃ RankModel hδ hAC hG :=
  Equiv.ofBijective (lowNameToRank hδ hAC hG)
    ⟨lowNameToRank_injective hδ hAC hG, lowNameToRank_surjective hδ hAC hG⟩

instance lowNameQuotient_nonempty : Nonempty (LowNameQuotient hδ hAC hG) :=
  Nonempty.map (lowNameRankEquiv hδ hAC hG).symm inferInstance

theorem lowNameRankEquiv_mem_iff (x y : LowNameQuotient hδ hAC hG) :
    lowNameRankEquiv hδ hAC hG x ∈ lowNameRankEquiv hδ hAC hG y ↔ x ∈ y :=
  (localInclusion hδ hAC hG).mem_iff x.val y.val

theorem lowNameQuotient_models_zfc : (LowNameQuotient hδ hAC hG)↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖 := by
  let := rankModel_models_zfc hδ hAC hG
  constructor
  intro φ hφ
  apply (eval_membershipIso (lowNameRankEquiv hδ hAC hG)
    (lowNameRankEquiv_mem_iff hδ hAC hG) φ ![] Empty.elim).mpr
  have hs := Theory.models (RankModel hδ hAC hG) 𝗭𝗙𝗖 hφ
  change φ.Eval ![] Empty.elim at hs
  have hf : (lowNameRankEquiv hδ hAC hG) ∘ (Empty.elim : Empty → LowNameQuotient hδ hAC hG) =
      Empty.elim := funext fun x ↦ Empty.elim x
  simpa only [hf, Matrix.empty_eq] using hs

end WoodinEndpointModel
end ZFVP
