import ZFVP.ModelTheory.ForcingNormalizedSupportCodes
import ZFVP.ModelTheory.WoodinNormalizedCode
import ZFVP.ModelTheory.WoodinDirectIndex
import ZFVP.ModelTheory.ForcingCanonicalTransport

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinNormalizedSupportCodes (θ : V) : V :=
  forcingNormalizedSupportCodes θ (woodinIterationPrefix θ) (woodinNormalizationHistory θ)

noncomputable def woodinNormalizedSupportOrder (θ : V) : V :=
  forcingNormalizedSupportOrder θ (woodinIterationPrefix θ) (woodinNormalizationHistory θ)

noncomputable def woodinNormalizedSupportMap (θ : V) : V :=
  forcingNormalizedSupportMap θ (woodinIterationPrefix θ) (woodinNormalizationHistory θ)

noncomputable def woodinNormalizedSupportEncode (θ : V) : V := converseGraph (woodinNormalizedSupportMap θ)

noncomputable def woodinNormalizedSupportTop (θ : V) : V :=
  (woodinNormalizedSupportEncode θ) ‘ ((forcingCodet (woodinNormalizedStageCode θ)) ‘ θ)

instance woodinNormalizedSupportCodes_definable : ℒₛₑₜ-function₁[V] woodinNormalizedSupportCodes := by
  unfold woodinNormalizedSupportCodes
  definability

instance woodinNormalizedSupportOrder_definable : ℒₛₑₜ-function₁[V] woodinNormalizedSupportOrder := by
  unfold woodinNormalizedSupportOrder
  definability

instance woodinNormalizedSupportMap_definable : ℒₛₑₜ-function₁[V] woodinNormalizedSupportMap := by
  unfold woodinNormalizedSupportMap
  definability

instance woodinNormalizedSupportEncode_definable : ℒₛₑₜ-function₁[V] woodinNormalizedSupportEncode := by
  unfold woodinNormalizedSupportEncode
  definability

instance woodinNormalizedSupportTop_definable : ℒₛₑₜ-function₁[V] woodinNormalizedSupportTop := by
  unfold woodinNormalizedSupportTop
  definability

theorem woodinNormalized_direct_poset {θ : V} [IsOrdinal θ]
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    (forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ =
      forcingMapFixedPoints ((forcingCodeP (forcingDirectCode θ (woodinIterationPrefix θ))) ‘ θ)
        (forcingNormalizationDirectMap θ (woodinIterationPrefix θ) (woodinNormalizationHistory θ)) := by
  unfold woodinNormalizedStageCode forcingNormalizedCode
  rw [forcingCodeP_code, forcingNormalizationCarriers_value (mem_succ_self θ),
    woodinNormalizationHistory_value (mem_succ_self θ), woodinIterationRec_direct h0 hlim hinac,
    kpair.π₁_kpair, woodinNormalizationRec_rule]
  simp only [woodinNormalizationRule, ite_eq_right h0, ite_eq_right hlim, ite_eq_left hinac]

theorem woodinNormalized_direct_order {θ : V} [IsOrdinal θ]
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    (forcingCodeR (woodinNormalizedStageCode θ)) ‘ θ =
      forcingOrderRestriction
        (forcingMapFixedPoints ((forcingCodeP (forcingDirectCode θ (woodinIterationPrefix θ))) ‘ θ)
          (forcingNormalizationDirectMap θ (woodinIterationPrefix θ) (woodinNormalizationHistory θ)))
        ((forcingCodeR (forcingDirectCode θ (woodinIterationPrefix θ))) ‘ θ) := by
  unfold woodinNormalizedStageCode forcingNormalizedCode
  rw [forcingCodeR_code, forcingNormalizationOrders_value (mem_succ_self θ),
    forcingNormalizationCarriers_value (mem_succ_self θ),
    woodinNormalizationHistory_value (mem_succ_self θ), woodinIterationRec_direct h0 hlim hinac,
    kpair.π₁_kpair, woodinNormalizationRec_rule]
  simp only [woodinNormalizationRule, ite_eq_right h0, ite_eq_right hlim, ite_eq_left hinac]

theorem woodinNormalizedSupportMap_isomorphism {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    IsForcingIsomorphism (woodinNormalizedSupportCodes θ) (woodinNormalizedSupportOrder θ)
      ((forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ)
      ((forcingCodeR (woodinNormalizedStageCode θ)) ‘ θ) (woodinNormalizedSupportMap θ) := by
  have hx := woodinIterationExit hΩ hAC
  have hs := woodinIterationPrefix_of_stages (fun i hi ↦ (hx.2.1 i (hθ i hi)).1)
  rw [woodinNormalized_direct_poset h0 hlim hinac, woodinNormalized_direct_order h0 hlim hinac]
  exact forcingNormalizedSupportMap_isomorphism (woodinNormalizationHistory_actual_prefix hΩ hAC hθ) hs.code

theorem woodinNormalizedSupportOrder_preorder {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    IsForcingPreorder (woodinNormalizedSupportCodes θ) (woodinNormalizedSupportOrder θ) := by
  have hx := woodinIterationExit hΩ hAC
  have hs := woodinIterationPrefix_of_stages (fun i hi ↦ (hx.2.1 i (hθ i hi)).1)
  exact forcingNormalizedSupportOrder_preorder (woodinNormalizationHistory_actual_prefix hΩ hAC hθ) hs.code

/-- The direct-stage endpoint bounds earlier carriers and hence the compressed codes. -/
theorem woodinNormalizedSupport_rank {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    IsChoicelessInaccessible θ ∧ woodinNormalizedSupportCodes θ ⊆ hierarchy θ ∧
      woodinNormalizedSupportOrder θ ⊆ hierarchy θ := by
  have hx := woodinIterationExit hΩ hAC
  have hs := woodinIterationPrefix_of_stages (fun i hi ↦ (hx.2.1 i (hθ i hi)).1)
  have he := hs.index_eq_regular_limit hlim hinac.regular
  have ht : IsChoicelessInaccessible θ := he.symm ▸ hinac
  have hP : ∀ i ∈ θ, (forcingCodeP (woodinIterationPrefix θ)) ‘ i ∈ hierarchy θ := by
    intro i hi
    have hK : (woodinIterationCardinalPrefix θ) ‘ i ∈ θ :=
      (congrArg (fun z ↦ (woodinIterationCardinalPrefix θ) ‘ i ∈ z) he).mpr (hs.cardinal_mem_limit hlim hi)
    have hp := hs.small i hi θ ht
    simp only [woodinIterationStage, woodinStagePoset_code, woodinStageCardinal_code] at hp
    exact hp hK
  have hn := woodinNormalizationHistory_actual_prefix hΩ hAC hθ
  exact ⟨ht, forcingNormalizedSupportCodes_subset_hierarchy hn hlim hP,
    forcingNormalizedSupportOrder_subset_hierarchy hn hlim hP⟩

theorem woodinNormalizedSupportMap_transport {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    IsCanonicalForcingTransport (woodinNormalizedSupportCodes θ) (woodinNormalizedSupportOrder θ)
      ((forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ)
      ((forcingCodeR (woodinNormalizedStageCode θ)) ‘ θ) (woodinNormalizedSupportMap θ) :=
  (woodinNormalizedSupportMap_isomorphism hΩ hAC hθ h0 hlim hinac).canonicalTransport

theorem woodinNormalizedSupportEncode_roundtrip {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    (∀ a ∈ woodinNormalizedSupportCodes θ,
      (woodinNormalizedSupportEncode θ) ‘ ((woodinNormalizedSupportMap θ) ‘ a) = a) ∧
    (∀ f ∈ (forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ,
      (woodinNormalizedSupportMap θ) ‘ ((woodinNormalizedSupportEncode θ) ‘ f) = f) := by
  have hi := woodinNormalizedSupportMap_isomorphism hΩ hAC hθ h0 hlim hinac
  exact ⟨fun _ ha ↦ hi.inverse_value ha, fun _ hf ↦ hi.value_inverse hf⟩

theorem woodinNormalizedSupportTop_spec {Ω θ : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    IsForcingTop (woodinNormalizedSupportCodes θ) (woodinNormalizedSupportOrder θ)
      (woodinNormalizedSupportTop θ) := by
  let := hΩ.inaccessible.1
  let := IsOrdinal.of_mem hθ
  have hi := woodinNormalizedSupportMap_isomorphism hΩ hAC
    (IsOrdinal.toIsTransitive.transitive _ hθ) h0 hlim hinac
  exact hi.inverse.map_top ((woodinNormalizedStageCode_valid hΩ hAC hθ).system.tops.top θ (mem_succ_self θ))

end ZFVP
