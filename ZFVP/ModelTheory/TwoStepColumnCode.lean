import ZFVP.ModelTheory.TwoStepIterationColumns
import ZFVP.SetTheory.ForcingIterationCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Compose the new column with an iterand before inserting its stage index. -/
noncomputable def forcingTwoStepColumnCode (θ s C T ρ F M one Q S u : V) : V :=
  forcingIterationCodeNext θ s (twoStepConditions C T Q u) (twoStepOrder C T Q S u)
    (forcingComposeProjectionColumn θ ρ (twoStepProjection C T Q u))
    (forcingComposeSectionColumn θ F (twoStepSection C u))
    (forcingTwoStepLiftColumn θ (twoStepConditions C T Q u) (forcingCodeP s) M) ⟨one, u⟩ₖ

theorem forcingTwoStepColumnCode_valid {θ s C T ρ F M one Q S u : V}
    (h : IsForcingIterationCode θ s)
    (c : IsForcingIterationColumn θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s)
      (forcingCodeE s) (forcingCodeL s) (forcingCodet s) C T ρ F M one)
    (hQ : IsForcingIterand C T Q S u) :
    IsForcingIterationCode (succ θ) (forcingTwoStepColumnCode θ s C T ρ F M one Q S u) :=
  h.extend (c.twoStep h.system hQ)

theorem forcingTwoStepColumnCode_extends {θ s : V} (h : IsForcingIterationCode θ s)
    (C T ρ F M one Q S u : V) :
    ForcingCodeExtends s (forcingTwoStepColumnCode θ s C T ρ F M one Q S u) :=
  h.extends_next _ _ _ _ _ _

theorem forcingTwoStepColumnCode_bound_table {θ s C T ρ F M one Q S B N i I : V}
    (c : IsForcingIterationColumn θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s)
      (forcingCodeE s) (forcingCodeL s) (forcingCodet s) C T ρ F M one)
    (hi : i ∈ θ)
    (hb : IsCoherentForcingBound θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s) B i I)
    (hc : IsSectionCompatibleForcingBound θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s)
      (forcingCodeE s) B i I)
    (b : IsCoherentForcingBoundColumn θ (forcingCodeP s) (forcingCodeR s) B C T ρ N i I)
    (bc : IsSectionCompatibleBoundColumn θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s) B F N i I)
    (hQ : IsForcingIterand C T Q S ∅)
    (hU : ∀ f, IsForcingDirectedFamily (twoStepConditions C T Q ∅) (twoStepOrder C T Q S ∅) I f →
      ∀ q ∈ C, (∀ a ∈ I, ⟨q, kpair.π₁ (f ‘ a)⟩ₖ ∈ T) →
      twoStepUnionBound I q f ∈ twoStepConditions C T Q ∅ ∧
        ∀ a ∈ I, ⟨twoStepUnionBound I q f, f ‘ a⟩ₖ ∈ twoStepOrder C T Q S ∅) :
    let z := forcingTwoStepColumnCode θ s C T ρ F M one Q S ∅
    let B' := forcingFamilyNext θ B (forcingSuccessorBound (twoStepConditions C T Q ∅)
      ((forcingCodeP s) ‘ i) (twoStepProjection C T Q ∅) N I)
    IsCoherentForcingBound (succ θ) (forcingCodeP z) (forcingCodeR z) (forcingCodeπ z) B' i I ∧
      IsSectionCompatibleForcingBound (succ θ) (forcingCodeP z) (forcingCodeR z) (forcingCodeπ z)
        (forcingCodeE z) B' i I := by
  have hcol := b.twoStep hi c.functions.projection c.order.preorder c.tops.top hQ hU
  have hsec := bc.twoStep hb c.functions.sectionMap c.order.preorder c.tops.top hQ
  simpa only [forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeP_code,
    forcingCodeR_code, forcingCodeπ_code, forcingCodeE_code] using
      And.intro (hb.extend hcol hi) (hc.extend hcol hsec hi)

end ZFVP
