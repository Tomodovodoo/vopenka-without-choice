import ZFVP.ModelTheory.WoodinNormalizationClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The actual source prefix with its carriers and maps restricted by normalization. -/
noncomputable def woodinNormalizedPrefixCode (θ : V) : V :=
  forcingNormalizedCode θ (woodinIterationPrefix θ) (woodinNormalizationHistory θ)

instance woodinNormalizedPrefixCode_definable : ℒₛₑₜ-function₁[V] woodinNormalizedPrefixCode := by
  unfold woodinNormalizedPrefixCode
  definability

/-- The normalized code including the completed stage at θ. -/
noncomputable def woodinNormalizedStageCode (θ : V) : V :=
  forcingNormalizedCode (succ θ) (kpair.π₁ (woodinIterationRec θ)) (woodinNormalizationHistory (succ θ))

instance woodinNormalizedStageCode_definable : ℒₛₑₜ-function₁[V] woodinNormalizedStageCode := by
  unfold woodinNormalizedStageCode
  definability

theorem woodinNormalizedPrefixCode_valid {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    IsForcingIterationCode θ (woodinNormalizedPrefixCode θ) := by
  have hx := woodinIterationExit hΩ hAC
  have hs := woodinIterationPrefix_of_stages (fun i hi ↦ (hx.2.1 i (hθ i hi)).1)
  exact (woodinNormalizationHistory_actual_prefix_liftClosed hΩ hAC hθ).code
    (woodinNormalizationHistory_actual_prefix hΩ hAC hθ) hs.code

theorem woodinNormalizedStageCode_valid {Ω θ : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω) :
    IsForcingIterationCode (succ θ) (woodinNormalizedStageCode θ) := by
  let := hΩ.inaccessible.1
  let := IsOrdinal.of_mem hθ
  exact (woodinNormalizationHistory_liftClosed hΩ hAC θ hθ).code
    (woodinNormalizationHistory_family hΩ hAC θ hθ) ((woodinIterationExit hΩ hAC).2.1 θ hθ).1.code

end ZFVP
