import ZFVP.ModelTheory.WoodinInitialStage
import ZFVP.ModelTheory.SaturatedQuotientClosureTransfer
import ZFVP.ModelTheory.IdentityQuotientClosureForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem identity_forcingSplitProjection (P R : V) :
    IsForcingSplitProjection P R P R (identity P) (identity P) := by
  refine ⟨⟨identity_mem_function P, ?_, ?_⟩, identity_mem_function P, ?_, ?_⟩
  · intro p hp q hq hpq
    simpa only [identity_value hp, identity_value hq] using hpq
  · intro q hq p hp hpq
    exact ⟨p, hp, by simpa only [identity_value hq] using hpq, identity_value hp⟩
  · intro p hp
    rw [identity_value hp, identity_value hp]
  · intro q hq p hp
    rw [identity_value hp, identity_value hq]

theorem saturatedWoodinPrefix_initial_quotient_closedBelow {P R one κ δ : V} [IsOrdinal κ]
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκδ : κ ⊆ δ)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ]))
    (hDC : ∀ p ∈ P, p ∈ forcingFormula P R dependentChoiceBelowFormula (standardTuple ![checkName one κ])) :
    let N := saturatedWoodinPrefixPosetName P R one κ δ
    let T := saturatedWoodinPrefixOrderName P R one κ δ
    ForcesProjectionQuotientClosedBelow P R one (twoStepConditions P R N ∅)
      (twoStepOrder P R N T ∅) (twoStepProjection P R N ∅) κ := by
  dsimp only
  have hi := saturatedWoodinPrefix_iterand hR ht hδ hP hκδ hκ
  apply saturatedWoodin_quotient_closure_forced hR ht (identity_forcingSplitProjection P R)
    hR ht hδ hP hκδ hκ rfl rfl (twoStep_projection hR ht hi) ?_ (subset_refl κ) hDC
    (identityQuotient_closedBelow_forced hR ht (identity_mem_function P) (fun _ hp ↦ identity_value hp))
  intro q hq
  have hp : kpair.π₁ q ∈ P := by
    simpa only [twoStepProjection_value hq] using function_value_mem (twoStepProjection_maps _ _ _ _) hq
  rw [identity_value hp, twoStepProjection_value hq]

theorem woodinInitialStage_seed_quotient_closedBelow {δ : V} (hδ : IsWoodinSupercompact δ) :
    let P := woodinStagePoset (woodinSeedStage : V)
    let R := woodinStageOrder (woodinSeedStage : V)
    let one := woodinStageTop (woodinSeedStage : V)
    let κ := woodinStageCardinal (woodinSeedStage : V)
    let c := woodinStageCardinal (woodinInitialStage : V)
    ForcesProjectionQuotientClosedBelow P R one
      (woodinStagePoset (woodinInitialStage : V)) (woodinStageOrder (woodinInitialStage : V))
      (twoStepProjection P R (saturatedWoodinPrefixPosetName P R one κ c) ∅) κ := by
  dsimp only
  have hs := woodinSeedStage_stage (V := V)
  let : IsOrdinal (woodinStageCardinal (woodinSeedStage : V)) := hs.2.2.1
  have hn := woodinSuccessorStep_preserves_below_supercompact hs woodinSeedStage_small hδ
    (by simpa only [woodinSeedStage, woodinStageCardinal_code] using woodinSeedCardinal_lt hδ)
  have hc : IsChoicelessInaccessible (woodinStageCardinal (woodinInitialStage : V)) := hn.2.2.1
  let := hc.1
  have hκc : woodinStageCardinal (woodinSeedStage : V) ∈ woodinStageCardinal (woodinInitialStage : V) := hn.2.2.2.1
  have hh := saturatedWoodinPrefix_initial_quotient_closedBelow hs.1 hs.2.1 hc
    (woodinSeedStage_small _ hc hκc) (IsOrdinal.toIsTransitive.transitive _ hκc)
    hs.2.2.2.1 hs.2.2.2.2
  simpa only [woodinInitialStage, woodinSuccessorStep, woodinSuccessorAt,
    woodinStagePoset_code, woodinStageOrder_code, woodinStageCardinal_code] using hh

end ZFVP
