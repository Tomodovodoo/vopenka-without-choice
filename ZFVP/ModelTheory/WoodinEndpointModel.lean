import ZFVP.ModelTheory.WoodinEndpointZFC

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace WoodinEndpointModel
variable {δ : V} (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) {G : Set V}
  (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ δ)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec δ))) ‘ δ) G)

noncomputable def context : ForcingContext V :=
  ⟨(forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ δ,
    (forcingCodeR (kpair.π₁ (woodinIterationRec δ))) ‘ δ,
    (forcingCodet (kpair.π₁ (woodinIterationRec δ))) ‘ δ, G,
    (woodinIteration_endpoint_valid hδ hAC).1.code.system.order.preorder δ (mem_succ_self δ),
    (woodinIteration_endpoint_valid hδ hAC).1.code.system.tops.top δ (mem_succ_self δ), hG⟩

abbrev RankModel := SetDomain (hierarchy ((context hδ hAC hG).check δ))

instance rankModel_nonempty : Nonempty (RankModel hδ hAC hG) :=
  (context hδ hAC hG).woodinEndpoint_rank_nonempty hδ hAC rfl rfl rfl

/-- The rank at the checked endpoint in the actual endpoint generic extension
satisfies the external standard ZFC theory. -/
theorem rankModel_models_zfc : (RankModel hδ hAC hG)↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖 :=
  (context hδ hAC hG).woodinEndpoint_rank_models_zfc hδ hAC rfl rfl rfl

/-- ZF also holds for every internally coded axiom in the endpoint rank. -/
theorem rank_internalZFModel : IsInternalZFModel (hierarchy ((context hδ hAC hG).check δ)) :=
  (context hδ hAC hG).woodinEndpoint_rank_internalZFModel hδ hAC rfl rfl rfl

end WoodinEndpointModel
end ZFVP
