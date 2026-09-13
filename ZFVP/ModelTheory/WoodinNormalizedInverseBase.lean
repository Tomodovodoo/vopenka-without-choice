import ZFVP.ModelTheory.ForcingNormalizedInverseOrder
import ZFVP.ModelTheory.WoodinNormalizedInverseCanonical

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinNormalizedInverseBase (θ : V) : V :=
  forcingInverseLimit θ (forcingCodeP (woodinNormalizedPrefixCode θ))
    (forcingCodeπ (woodinNormalizedPrefixCode θ)) (forcingCodeUniverse (woodinIterationPrefix θ))

noncomputable def woodinNormalizedInverseOrder (θ : V) : V :=
  forcingThreadOrder θ (forcingCodeR (woodinNormalizedPrefixCode θ)) (woodinNormalizedInverseBase θ)

instance woodinNormalizedInverseBase_definable : ℒₛₑₜ-function₁[V] woodinNormalizedInverseBase := by
  unfold woodinNormalizedInverseBase
  apply Language.DefinableFunction₄.comp <;> definability

instance woodinNormalizedInverseOrder_definable : ℒₛₑₜ-function₁[V] woodinNormalizedInverseOrder := by
  unfold woodinNormalizedInverseOrder
  apply Language.DefinableFunction₃.comp <;> definability

variable {Ω θ : V} [IsOrdinal θ]
local notation "s" => woodinIterationPrefix θ
local notation "m" => woodinNormalizationHistory θ
local notation "N" => woodinNormalizedInverseBase θ
local notation "T" => woodinNormalizedInverseOrder θ
local notation "P" => forcingInverseCodePoset θ s
local notation "R" => forcingInverseCodeOrder θ s
local notation "r" => forcingNormalizationInverseMap θ s m

theorem woodinNormalized_inverse_base_dictionary
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    forcingMapFixedPoints P r = N ∧ forcingOrderRestriction N R = T := by
  have hx := woodinIterationExit hΩ hAC
  have hs := woodinIterationPrefix_of_stages (fun i hi ↦ (hx.2.1 i (hθ i hi)).1)
  have hn := woodinNormalizationHistory_actual_prefix hΩ hAC hθ
  constructor
  · simpa only [forcingInverseCodePoset, forcingInverseCode, forcingThreadCode_poset,
      woodinNormalizedInverseBase, woodinNormalizedPrefixCode,
      forcingNormalizedCode, forcingCodeP_code, forcingCodeπ_code] using
      forcingNormalized_inverse_fixedPoints hn hs.code
  · simpa only [forcingInverseCodeOrder, forcingInverseCodePoset, forcingInverseCode, forcingThreadCode_order,
      woodinNormalizedInverseBase, woodinNormalizedInverseOrder, woodinNormalizedPrefixCode,
      forcingNormalizedCode, forcingCodeP_code, forcingCodeR_code, forcingCodeπ_code] using
      (forcingNormalized_inverse_threadOrder hn hs.code :
        forcingOrderRestriction _ (forcingThreadOrder θ _ (forcingInverseLimit θ _ _ (forcingCodeUniverse s))) = _)

theorem woodinNormalized_inverse_base_laws
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (h0 : ∅ ∈ θ) :
    IsForcingPreorder N T ∧ IsForcingTop N T (forcingInverseCodeTop θ s) := by
  have hx := woodinIterationExit hΩ hAC
  have hs := woodinIterationPrefix_of_stages (fun i hi ↦ (hx.2.1 i (hθ i hi)).1)
  have hn := woodinNormalizationHistory_actual_prefix hΩ hAC hθ
  obtain ⟨hr, ho, _⟩ := forcingNormalizationInverse_base hs.code hn h0
  obtain ⟨hb, he⟩ := woodinNormalized_inverse_base_dictionary hΩ hAC hθ
  have col := hs.code.system.inverseColumn h0 hs.code.subset_universe
  have ht : IsForcingTop P R (forcingInverseCodeTop θ s) := col.tops.top
  have hone : forcingInverseCodeTop θ s ∈ forcingMapFixedPoints P r := mem_sep_iff.mpr ⟨ht.1, ho⟩
  have hpre := forcingOrderRestriction_preorder col.order.preorder hr.inclusion
  change IsForcingPreorder (forcingMapFixedPoints P r)
    (forcingOrderRestriction (forcingMapFixedPoints P r) R) at hpre
  have htop := hr.top_of_mem ht hone
  rw [hb, he] at hpre htop
  exact ⟨hpre, htop⟩

theorem woodinNormalized_inverse_dictionary
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    let one := forcingInverseCodeTop θ s
    let card := woodinLimitCardinal (woodinIterationCardinalPrefix θ)
    let cut := woodinNamedPrefixCutoff N T one card (hartogsNumberName N T (checkName one card))
    let iter := saturatedHartogsPosetName N T one card cut
    let ord := saturatedHartogsOrderName N T one card cut
    (forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ = normalizedNameTwoStep N T one cut iter ∧
      (forcingCodeR (woodinNormalizedStageCode θ)) ‘ θ =
        nameTwoStepOrderOn N T ord (normalizedNameTwoStep N T one cut iter) := by
  let := hΩ.inaccessible.1
  obtain ⟨hb, hr⟩ := woodinNormalized_inverse_base_dictionary hΩ hAC
    (IsOrdinal.toIsTransitive.transitive _ hθ)
  have hh := woodinNormalizedStage_inverse_carrier_order hΩ hAC hθ h0 hlim hn
  dsimp only at hh ⊢
  rwa [hb, hr] at hh

end ZFVP
