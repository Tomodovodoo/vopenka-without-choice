import ZFVP.ModelTheory.NormalizedIsomorphismDefinability
import ZFVP.ModelTheory.WoodinSupportSuccessorTransport
import ZFVP.ModelTheory.WoodinNormalizedSuccessorMaps

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSupportSuccessorMap (θ : V) : V :=
  let P := (forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ
  let R := (forcingCodeR (woodinNormalizedStageCode θ)) ‘ θ
  let one := (forcingCodet (woodinNormalizedStageCode θ)) ‘ θ
  let δ := woodinPrefixCutoff P R one θ
  normalizedTwoStepIsoMap P R one δ (saturatedWoodinPrefixPosetName P R one θ δ)
    (woodinNormalizedSupportCodes θ) (woodinNormalizedSupportOrder θ) (woodinNormalizedSupportTop θ)
    (woodinNormalizedSupportEncode θ)

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

instance woodinSupportSuccessorMap_definable : ℒₛₑₜ-function₁[V] woodinSupportSuccessorMap := by
  unfold woodinSupportSuccessorMap
  dsimp only
  apply normalizedTwoStepIsoMap_comp <;> definability

variable {Ω θ : V}
local notation "A" => woodinNormalizedSupportCodes θ
local notation "B" => woodinNormalizedSupportOrder θ
local notation "top" => woodinNormalizedSupportTop θ
local notation "f" => woodinNormalizedSupportEncode θ

theorem woodinSupportSuccessorMap_isomorphism
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    let ε := woodinPrefixCutoff A B top θ
    let iter := saturatedWoodinPrefixPosetName A B top θ ε
    IsForcingIsomorphism
      ((forcingCodeP (woodinNormalizedStageCode (succ θ))) ‘ (succ θ))
      ((forcingCodeR (woodinNormalizedStageCode (succ θ))) ‘ (succ θ))
      (normalizedNameTwoStep A B top ε iter)
      (nameTwoStepOrderOn A B (saturatedWoodinPrefixOrderName A B top θ ε)
        (normalizedNameTwoStep A B top ε iter)) (woodinSupportSuccessorMap θ) :=
  woodinSupport_recursive_successor_isomorphism hΩ hAC hθ h0 hlim hinac

theorem woodinSupportSuccessorMap_value {z : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hz : z ∈ (forcingCodeP (woodinNormalizedStageCode (succ θ))) ‘ (succ θ)) :
    (woodinSupportSuccessorMap θ) ‘ z = normalizedTwoStepIsoValue A B top f z := by
  let := hΩ.inaccessible.1
  let := IsOrdinal.of_mem hθ
  have hc := (woodinNormalizedStage_successor_eq hΩ hAC hθ).1
  rw [woodinDirect_stage_cardinal hΩ hAC hθ h0 hlim hinac] at hc
  rw [hc] at hz
  exact normalizedTwoStepIsoMap_value hz

theorem woodinSupportSuccessorMap_prefix {z : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hz : z ∈ (forcingCodeP (woodinNormalizedStageCode (succ θ))) ‘ (succ θ)) :
    kpair.π₁ ((woodinSupportSuccessorMap θ) ‘ z) = f ‘ (kpair.π₁ z) := by
  rw [woodinSupportSuccessorMap_value hΩ hAC hθ h0 hlim hinac hz]
  exact normalizedTwoStepIsoValue_prefix A B top f z

theorem woodinSupportSuccessorMap_top
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    (woodinSupportSuccessorMap θ) ‘ ((forcingCodet (woodinNormalizedStageCode (succ θ))) ‘ (succ θ)) =
      ⟨top, ∅⟩ₖ := by
  let := hΩ.inaccessible.1
  let := IsOrdinal.of_mem hθ
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hsucc := hΩ.inaccessible.rankCriterion.2.2.1 θ hθ
  have hv := woodinNormalizedStageCode_valid hΩ hAC hsucc
  have hz := (hv.system.tops.top (succ θ) (mem_succ_self (succ θ))).1
  rw [woodinSupportSuccessorMap_value hΩ hAC hθ h0 hlim hinac hz,
    woodinNormalizedStage_successor_top hΩ hAC hθ,
    normalizedTwoStepIsoValue_empty_tail (woodinNormalizedSupportOrder_preorder hΩ hAC hsub)
      (woodinNormalizedSupportTop_spec hΩ hAC hθ h0 hlim hinac).1]
  rfl

end ZFVP
